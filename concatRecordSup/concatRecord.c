/* File: concatRecordSup/concatRecord.c
 * DateTime: Sat Oct  4 14:23:29 2025
 * Last checked in by: starritt
 *
 * SPDX-FileCopyrightText: 2009-2025 Australian Synchrotron
 * SPDX-License-Identifier: LGPL-3.0-only
 *
 * Contact details:
 * andrews@ansto.gov.au
 * 800 Blackburn Road, Clayton, Victoria 3168, Australia.
 *
 * Description:
 * This record allows the concatination of scalar and array constants, scalar
 * PVs and array PVs (such as compress, subArray and waveform records and also
 * other concat records) into an array record.
 *
 * The record can specify upto 100 inputs (IN00 to IN99).  If more than 100
 * values are required for concatination, then a hierachy of concat records
 * can be used.
 *
 * Since version 2.1, updated to support json links for input constants.
 * This make the concat record as is incompatible with earlier versions
 * of EPICS base.
 *
 * Author: Andrew Starritt
 *
 * Credits:
 * Derived, in part, from aSubRecord.c,v 1.1.2.2 2008/08/15 21:43:52 anj Exp
 * which inturn was derived from genSubRecord.
 *
 *      Original genSubRecord Author: Andy Foster
 *      aSubRecord Revised by: Andrew Johnson
 *
 * Also cribbed output handlining from the calcout record.
 *
 *      Author : Ned Arnold
 *      Based on recCalc.c by Julie Sander and Bob Dalesio
 */

#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <string.h>
#include <stdarg.h>

#include "alarm.h"
#include "callback.h"
#include "cantProceed.h"
#include "dbDefs.h"
#include "dbEvent.h"
#include "dbAccess.h"
#include "dbFldTypes.h"
#include "dbStaticLib.h"
#include "devSup.h"
#include "epicsExport.h"
#include "errlog.h"
#include "errMdef.h"
#include "menuFtype.h"
#include "recGbl.h"
#include "recSup.h"
#include "registryFunction.h"
#include "special.h"

#define GEN_SIZE_OFFSET
#include "concatRecord.h"
#undef  GEN_SIZE_OFFSET

/* Create RSET - Record Support Entry Table
 */
#define report              NULL
#define initialize          NULL
static long init_record (dbCommon *, int);
static long process (dbCommon *);
static long special (DBADDR *, int);
#define get_value           NULL
static long cvt_dbaddr (DBADDR *);
static long get_array_info (DBADDR *, long *, long *);
static long put_array_info (DBADDR *, long);
static long get_units (DBADDR *, char *);
static long get_precision (const DBADDR *, long *);
#define get_enum_str        NULL
#define get_enum_strs       NULL
#define put_enum_str        NULL
static long get_graphic_double (DBADDR *, struct dbr_grDouble *);
static long get_control_double (DBADDR *, struct dbr_ctrlDouble *);
#define get_alarm_double    NULL

rset concatRSET = {
   RSETNUMBER,
   report,
   initialize,
   init_record,
   process,
   special,
   get_value,
   cvt_dbaddr,
   get_array_info,
   put_array_info,
   get_units,
   get_precision,
   get_enum_str,
   get_enum_strs,
   put_enum_str,
   get_graphic_double,
   get_control_double,
   get_alarm_double
};

epicsExportAddress (rset, concatRSET);

static long init_record_pass0 (concatRecord *prec);
static long init_record_pass1 (concatRecord *prec);

static long fetch_values (concatRecord *prec);
static bool is_output_required (concatRecord *prec);
static void monitor (concatRecord *prec);
static void execOutput (concatRecord *prec);
static long writeValue (concatRecord *prec);
static long do_concat (concatRecord *prec);


#define VERSION         "3.1.1"
#define NUM_ARGS        100

/* Define first and last attribute type macros
 */
#define VFIRST          concatRecordV00
#define VLAST           concatRecordV99

#define MEFIRST         concatRecordME00
#define MELAST          concatRecordME99

#define NEFIRST         concatRecordNE00
#define NELAST          concatRecordNE99

#define MAX_ARRAY_SIZE  (10*1000*1000)


/* -----------------------------------------------------------------------------
 * Local types
 * -----------------------------------------------------------------------------
 */

/* Last/previous values so that we can post/monitor these.
 */
struct state_data {
   epicsUInt32 nord;                   /* Actual number elements */
   void *val;                          /* Value */
   epicsUInt32 inputNumber[NUM_ARGS];  /* Num. elements in NExx */
   void *inputValues[NUM_ARGS];        /* Input value Vxx */
};


typedef struct concatPrivate {
   /* Effective number of elements per input including padding.
    * Can be different to the NExx values.
    * A reference to this is held in prec->rpvt
    */
   epicsUInt32 number_available[NUM_ARGS];
   struct state_data alst;      /* Last archived values */
   struct state_data mlst;      /* Last monitored values */
} concatPrivate;


/* Common macro functions.
*/
#define MAX(a, b)           ((a) >= (b) ? (a) : (b))
#define MIN(a, b)           ((a) <= (b) ? (a) : (b))
#define LIMIT(x,low,high)   (MAX(low, MIN(x, high)))


/* -----------------------------------------------------------------------------
 * Local functions
 * -----------------------------------------------------------------------------
 */


/* -----------------------------------------------------------------------------
 * errlogPrintf wrapper function
 */
static void concatError (concatRecord *prec, const char *format, ...)
{
   char buffer[200];
   va_list args;

   va_start (args, format);
   vsnprintf (buffer, 200, format, args);
   va_end (args);

   errlogPrintf ("concat record (%s): %s\n", prec->name, buffer);
}                               /* concatError */


/* -----------------------------------------------------------------------------
 * Pads element i of the input array j with specified pad value.
 */
static void pad_input (concatRecord *prec, const int j, const int i)
{
   void *input;

   /* Generic code must be defined as a macro.
 */
#define NUMERIC_PAD(type)               \
{                                       \
   type *list;                          \
   list = (type *) input;               \
   list[i] = (type) prec->dfnv;         \
}

   input = (&prec->v00)[j];

   switch (prec->ftvl) {

      case menuFtypeSTRING:{
            char *list;
            list = (char *) input;
            strncpy ((char *) &(list[40 * i]), prec->dfsv, 40);
         }
         break;

      case menuFtypeCHAR:
         /* maybe this case should use the first character from
          * the dfsv field.
          */
         NUMERIC_PAD (epicsInt8);
         break;

      case menuFtypeUCHAR:
         NUMERIC_PAD (epicsUInt8);
         break;

      case menuFtypeSHORT:
         NUMERIC_PAD (epicsInt16);
         break;

      case menuFtypeUSHORT:
         NUMERIC_PAD (epicsUInt16);
         break;

      case menuFtypeLONG:
         NUMERIC_PAD (epicsInt32);
         break;

      case menuFtypeULONG:
         NUMERIC_PAD (epicsUInt32);
         break;

      case menuFtypeFLOAT:
         NUMERIC_PAD (epicsFloat32);
         break;

      case menuFtypeDOUBLE:
         NUMERIC_PAD (epicsFloat64);
         break;

      case menuFtypeENUM:
         NUMERIC_PAD (epicsEnum16);
         break;

      default:
         concatError (prec, "pad_input %02d [%d] - unexpected FTVL %d",
                      j, i, prec->ftvl);
         break;
   }

#undef NUMERIC_PAD
}                               /* pad_input */


/* -----------------------------------------------------------------------------
 * Fetches the values from the single input link j.
 * Note: j goes in range 0 .. 99.
 */
static long fetch_one_value (concatRecord *prec, const int j)
{
   concatPrivate *rpvt = (concatPrivate *) prec->rpvt;

   /* Note on field access:
    *
    *   prec->me00       refers to field ME00 (which happends to be epicsUInt32)
    *   &prec->me00      is not just an address but is an epicsUInt32* pointer to prec->me00.
    *  (&prec->me00)[j]  deferences the implicit type pointer to access ME<j>
    *
    * The advantage of this is we don't make any assumptions about the field type/size.
    */
   const epicsUInt32 max_elements = (&prec->me00)[j];     /* more readable alias */

   long nRequst = max_elements;
   long status = dbGetLink (&(&prec->in00)[j], prec->ftvl,
                            (&prec->v00)[j], 0, &nRequst);

   /* For constants and JSON (and others) nRequest is zero, which is why
    * fetch_values () skips over these.
    * The value setup during initialisation defines number fetched,
    */
   const epicsUInt32 number_fetched = nRequst;
   (&prec->ne00)[j] = number_fetched;

   epicsUInt32 number_available = number_fetched;
   concatMODE action = concatMODE_Fail;

   /* Fetch successful?
    */
   if (status == 0) {

      /* Yes - ensure sensible number_fetched.
       */
      if (number_available > max_elements) {
         number_available = max_elements;
      }

      /* Did we get all the expected values?
       */
      if (number_available < max_elements) {
         /* Reduced input - i.e. less than expected maximum.
          */
         status = -1;
         action = prec->riem;
      }

   } else {
      /* Fetch failed - no input.
       */
      status = -1
      number_available = 0;
      action = prec->niem;
   }

   /* Did - some problem occur?
    */
   if (status != 0) {

      switch (action) {

         case concatMODE_Fail:
            /* Some input missing - fail.
             */
            status = -1;
            number_available = 0;
            break;

         case concatMODE_Skip:
            /* Some input missing -just ignore.
             */
            status = 0;
            break;

         case concatMODE_Pad:
            /* Pad input with default value upto maximum number of elements.
             */
            {
               int i;
               for (i = number_available; i < max_elements; i++) {
                  pad_input (prec, j, i);
               }
            }
            number_available = max_elements;
            status = 0;
            break;

         default:
            status = -1;
            number_available = 0;
            concatError (prec, "fetch_one_value %02d - unexpected action %d",
                         j, action);
            break;
      }
   }

   rpvt->number_available[j] = number_available;
   return status;
}                               /* fetch_one_value */


/* -----------------------------------------------------------------------------
 * Returns true if any element delta exceeds deadband (if numeric) otherwise
 * returns true if different.
 */
static bool field_compare (const void *s1, const void *s2, const int num,
                           const epicsEnum16 ftvl, const double deadband)
{
   bool result;
   size_t size;

/* Generic compare code must be defined as a macro
 */
#define COMPARE(type)                   \
{                                       \
   type *t1 = (type *) s1;              \
   type *t2 = (type *) s2;              \
   result = false;                      \
   int j;                               \
   for (j = 0; j < num; j++) {          \
      double delta = t1[j] - t2[j];     \
      if (delta < 0.0) {                \
         delta = -delta;                \
      }                                 \
      if (delta > deadband) {           \
         result = true;                 \
         break;                         \
      }                                 \
   }                                    \
}

   switch (ftvl) {

      case menuFtypeCHAR:
         COMPARE (epicsInt8);
         break;

      case menuFtypeUCHAR:
         COMPARE (epicsUInt8);
         break;

      case menuFtypeSHORT:
         COMPARE (epicsInt16);
         break;

      case menuFtypeUSHORT:
         COMPARE (epicsUInt16);
         break;

      case menuFtypeLONG:
         COMPARE (epicsInt32);
         break;

      case menuFtypeULONG:
         COMPARE (epicsUInt32);
         break;

      case menuFtypeFLOAT:
         COMPARE (epicsFloat32);
         break;

      case menuFtypeDOUBLE:
         COMPARE (epicsFloat64);
         break;

      case menuFtypeENUM:
         COMPARE (epicsEnum16);
         break;

      default:
         size = (size_t) num *dbValueSize (ftvl);
         result = memcmp (s1, s2, size);
         result = result != 0 ? true : false;
   }

   return result;

#undef COMPARE
}                               /* field_cmp */


/* -----------------------------------------------------------------------------
 */
static void field_copy (void *dest, const void *src, const int num,
                        const epicsEnum16 ftvl)
{
   size_t size;

   size = (size_t) num *dbValueSize (ftvl);
   memcpy (dest, src, size);
}                               /* field_copy */


/* -----------------------------------------------------------------------------
 */
static long init_record_pass0 (concatRecord * prec)
{
   concatPrivate *rpvt;
   int j;

///   prec->vers = VERSION;

   /* Allocate memory for this record's private data.
    * Store away the private data for this record into the EPICS record.
    */
   rpvt = (concatPrivate *) callocMustSucceed
         (1, sizeof (concatPrivate), "concatRecord::init_record_pass0");

   prec->rpvt = rpvt;

   /* Allocate memory for value array.
    * Must be at least 1.
    */
   if (prec->nelm <= 0) {
      prec->nelm = 1;
   }

   if (prec->ftvl > DBF_ENUM) {
      prec->ftvl = DBF_UCHAR;
   }

   const size_t size = dbValueSize (prec->ftvl);

   prec->val =
         callocMustSucceed (prec->nelm, size, "concatRecord::init_record_pass0");
   prec->nord = 0;

   rpvt->mlst.val =
         callocMustSucceed (prec->nelm, size, "concatRecord::init_record_pass0");
   rpvt->mlst.nord = 0;

   rpvt->alst.val =
         callocMustSucceed (prec->nelm, size, "concatRecord::init_record_pass0");
   rpvt->alst.nord = 0;

   /* Allocate memory for the input arrays.
    *
    * Determine max num of input elements
    */
   size_t max_elements = MAX_ARRAY_SIZE / size;

   for (j = 0; j < NUM_ARGS; j++) {

      epicsUInt32 count = (&prec->me00)[j];

      if (count > max_elements) {
         count = max_elements;
         (&prec->me00)[j] = count;
         concatError (prec, "field ME%02d too large - truncated to %d elements",
                      j, count);
      }

      /* Must be at least one element when we allocate memory.
       */
      if (count <= 0) {
         count = 1;
      }

      (&prec->v00)[j] =
            callocMustSucceed (count, size, "concatRecord::init_record_pass0");
      (&prec->ne00)[j] = 0;

      rpvt->number_available[j] = 0;

      rpvt->mlst.inputValues[j] =
            callocMustSucceed (count, size, "concatRecord::init_record_pass0");
      rpvt->mlst.inputNumber[j] = 0;

      rpvt->alst.inputValues[j] =
            callocMustSucceed (count, size, "concatRecord::init_record_pass0");
      rpvt->alst.inputNumber[j] = 0;
   }

   return 0;
}                               /* init_record_pass0 */


/* -----------------------------------------------------------------------------
 */
static long init_record_pass1 (concatRecord * prec)
{
   concatPrivate *rpvt = (concatPrivate *) prec->rpvt;
   concatdset *pconcatDSET = (concatdset*) prec->dset;

   if (!pconcatDSET) {
      recGblRecordError(S_dev_noDSET, (void *)prec, "concat:init_record");
      return S_dev_noDSET;
   }

   /* must have write defined */
   if ((pconcatDSET->common.number < 5) || (pconcatDSET->write == NULL)) {
      recGblRecordError(S_dev_missingSup, (void *)prec, "concat:init_record");
      return S_dev_missingSup;
   }

   /* Initialize Input Links
    */
   int status = 0;
   int total = 0;
   int j;
   for (j = 0; j < NUM_ARGS; j++) {
      struct link *plink = &(&prec->in00)[j];
      short dbr = prec->ftvl;
      long n = (&prec->me00)[j];

      /* The ME00, ME01 ... ME99 fields default to 0.
        * If these values are 0 and there is anything in the input link, then set
        * to 1 (as opposed to defaulting to 1 and ignoring when link is empty).
        */
      switch (plink->type) {

         case CONSTANT:
            if ((n == 0) && plink->value.constantStr) {
               n = 1;
            }
            break;

         case JSON_LINK:
            if ((n == 0) && plink->value.json.string) {
               n = 1;
            }
            break;

         case PV_LINK:
         case CA_LINK:
         case DB_LINK:
            if (n == 0) {
               n = 1;
            }
            break;

         default:
            n = 0;
            rpvt->number_available[j] = 0;
            recGblRecordError (S_db_badField, (void *) prec,
                               "concatRecord(init_record) Illegal INPUT LINK");
            status = S_db_badField;
            break;
      }

      /* ... and update the MExx field
        */
      (&prec->me00)[j]= n;

      dbLoadLinkArray(plink, dbr, (&prec->v00)[j], &n);
      if (n > 0) {
         (&prec->ne00)[j] = n;
         rpvt->number_available[j] = n;
      }

      total += (&prec->me00)[j];
   }                            /* loop */

   if (total > prec->nelm) {
      concatError
            (prec, "warning: sum of max MEnn values (%d) exceeds allocated (NELM=%d) size",
             total, prec->nelm);
   }

   prec->epvt = eventNameToHandle (prec->oevt);

   if (pconcatDSET->common.init_record) {
      pconcatDSET->common.init_record (prec);
   }

   prec->udf = TRUE;
   return status;
}                               /* init_record_pass1 */


/* -----------------------------------------------------------------------------
 * Support functions
 * -----------------------------------------------------------------------------
 */
/* -----------------------------------------------------------------------------
 */
static long init_record (dbCommon * pCommon, int pass)
{
   /* Set the VERSion attribute - this replaces the VERS field.
    */
   dbPutAttribute("concat", "VERS", VERSION);

   concatRecord *prec = (concatRecord*) pCommon;

   long status;

   switch (pass) {
      case 0:
         status = init_record_pass0 (prec);
         break;

      case 1:
         status = init_record_pass1 (prec);
         break;

      default:
         concatError (prec, "init_record pass %d", pass);
         status = S_db_errArg;
   }

   return status;
}                               /* init_record */


/* -----------------------------------------------------------------------------
 */
static long process (dbCommon * pCommon)
{
   concatRecord *prec = (concatRecord*) pCommon;

   const unsigned char pact = prec->pact;

   if (!prec->pact) {
      prec->pact = TRUE;

      long status = fetch_values (prec);
      if (!status) {
         status = do_concat (prec);
      }

      /* checking for alarms is n/a, there is no HIHI, LOLO etc. */

      if (!pact) {
         /* Update the timestamp before writing output values so it
          * will be up to date if any downstream records fetch it via TSEL.
          */
         recGblGetTimeStamp (prec);
      }

      /* Check for output link execution
       */
      bool doOutput;
      switch (prec->oopt) {
         case concatOOPT_Every_Time:
            doOutput = true;
            break;
         case concatOOPT_On_Change:
            doOutput = is_output_required (prec);
            break;
         case concatOOPT_Never:
            doOutput = false;
            break;
         default:
            doOutput = false; /* unknown state */
            break;
      }

      if (doOutput) {
         /* Unlike calcout, there is no delay option .... yet.
          */
         prec->pact = FALSE;
         execOutput (prec);
         if (prec->pact) return 0;
         prec->pact = TRUE;
      }
   }
   else { /* pact == TRUE */
      /* Update timestamp again for asynchronous devices \
       */
      recGblGetTimeStamp (prec);

      /* Device Support is asynchronous
       */
      writeValue (prec);
   }

   /* Check event list.
    */
   monitor (prec);

   /* Process the forward scan link record.
    */
   recGblFwdLink (prec);

   prec->pact = FALSE;

   return 0;
}                               /* process */

/* -----------------------------------------------------------------------------
 */
static long special (DBADDR *paddr, int after)
{
   concatRecord *prec = (concatRecord *)paddr->precord;
   const int fieldIndex = dbGetFieldIndex (paddr);

   if (!after) return 0;

   switch (fieldIndex) {
      case concatRecordOEVT:
         prec->epvt = eventNameToHandle (prec->oevt);
         return 0;

      default:
         recGblDbaddrError (S_db_badChoice, paddr, "calc: special");
         return (S_db_badChoice);
   }
}                               /* special */

/* -----------------------------------------------------------------------------
 */
static long fetch_values (concatRecord * prec)
{
   int j;

   /* Get the input link values
    */
   for (j = 0; j < NUM_ARGS; j++) {

      const epicsUInt32 maxElements = (&prec->me00)[j];
      const struct link *plink = &(&prec->in00)[j];
      const short linkType = plink->type;

      /* Recall we need at least 1 for active input links.
       * Also constant and json links are already "fetched".
       */
      if ((linkType != CONSTANT) && (linkType != JSON_LINK) && (maxElements > 0)) {
         long status = fetch_one_value (prec, j);
         if (status) {
            concatError (prec, "fetch_values input %02d failed", j);
            return status;
         }
      }
   }
   return 0;
}                               /* fetch_values */


/* -----------------------------------------------------------------------------
 */
static long do_concat (concatRecord * prec)
{
   concatPrivate *rpvt = (concatPrivate *) prec->rpvt;

   long status = 0;
   epicsUInt8 *val;
   int size;
   int number;
   int room;
   int j;
   int n;

   /* Treat val as a unsigned 8 bit type array.
    */
   val = (epicsUInt8 *) prec->val;

   size = (int) dbValueSize (prec->ftvl);

   number = 0;
   for (j = 0; j < NUM_ARGS; j++) {

      /* How much room left?
       */
      room = prec->nelm - number;
      if (room <= 0) {
         break;
      }

      /* Extract effective number of available elements, limited by
       * amount of room left.
       */
      n = LIMIT (rpvt->number_available[j], 0, room);
      if (n > 0) {
         memcpy (&(val[number * size]), (&prec->v00)[j],
                 (size_t) n * size);
         number += n;
      }
   }

   prec->nord = number;
   prec->udf = FALSE;
   return status;
}                               /* do_concat */


/* -----------------------------------------------------------------------------
 */
static void execOutput (concatRecord *prec)
{
   if (prec->udf) {
      recGblSetSevr (prec, UDF_ALARM, prec->udfs);
   }

   writeValue(prec);

   /* post output event if set */
   if (prec->epvt) postEvent (prec->epvt);
}                               /* execOutput */

/* -----------------------------------------------------------------------------
 */
static long writeValue (concatRecord *prec)
{
   concatdset* pconcatDSET = (concatdset *)prec->dset;

   if (!pconcatDSET || !pconcatDSET->write) {
      errlogPrintf("%s DSET write does not exist\n", prec->name);
      recGblSetSevrMsg (prec, SOFT_ALARM, INVALID_ALARM, "DSET write does not exist");
      prec->pact = TRUE;
      return (-1);
   }

   long status = pconcatDSET->write (prec);
   return status;
}                               /* writeValue */


/* -----------------------------------------------------------------------------
 */
static long get_units (DBADDR *paddr, char *units)
{
   concatRecord *prec = (concatRecord *) paddr->precord;

   strncpy (units, prec->egu, DB_UNITS_SIZE);
   return 0;
}                               /* get_units */


/* -----------------------------------------------------------------------------
 */
static long get_precision (const DBADDR* paddr, long *precision)
{
   concatRecord *prec = (concatRecord *) paddr->precord;

   *precision = prec->prec;
   recGblGetPrec (paddr, precision);
   return 0;
}                               /* get_precision */


/* -----------------------------------------------------------------------------
 */
static long get_graphic_double (DBADDR *paddr, struct dbr_grDouble *pgd)
{
   concatRecord *prec = (concatRecord *) paddr->precord;
   const int fieldIndex = dbGetFieldIndex (paddr);

   if (fieldIndex == concatRecordVAL ||
       fieldIndex == concatRecordLOPR ||
       fieldIndex == concatRecordHOPR ||
       (fieldIndex >= VFIRST && fieldIndex <= VLAST)) {
      pgd->lower_disp_limit = prec->lopr;
      pgd->upper_disp_limit = prec->hopr;
   } else if (fieldIndex == concatRecordPREC) {
      pgd->lower_disp_limit = 0;
      pgd->upper_disp_limit = 15;
   } else {
      recGblGetGraphicDouble (paddr, pgd);
   }
   return 0;
}                               /* get_graphic_double */


/* -----------------------------------------------------------------------------
 */
static long get_control_double (DBADDR *paddr, struct dbr_ctrlDouble *pcd)
{
   concatRecord *prec = (concatRecord *) paddr->precord;
   const int fieldIndex = dbGetFieldIndex (paddr);

   if (fieldIndex == concatRecordVAL ||
       (fieldIndex >= VFIRST && fieldIndex <= VLAST)) {
      pcd->lower_ctrl_limit = prec->lopr;
      pcd->upper_ctrl_limit = prec->hopr;
   } else if (fieldIndex == concatRecordPREC) {
      pcd->lower_ctrl_limit = 0;
      pcd->upper_ctrl_limit = 15;
   } else {
      recGblGetControlDouble (paddr, pcd);
   }
   return 0;
}                               /* get_control_double */

/* -----------------------------------------------------------------------------
 * This checks if the VALue has changes sufficiently to warrent wrting to OUT.
 * This gets replicated somewhat in monitor/monitor_field_pair, at least
 * for the VAL field. Maybe we can refactor the code and or cache the result.
 */
static bool is_output_required (concatRecord *prec)
{
   concatPrivate* rpvt = (concatPrivate *) prec->rpvt;
   bool changed;

   /* If no. elements has changed, then we do an updated.
    */
   if (rpvt->mlst.nord != prec->nord) return true;

   /* No. of elements unchanged - do an element by element comparison.
    */
   changed = field_compare (rpvt->mlst.val, prec->val, prec->nord,
                            prec->ftvl, prec->mdel);
   return changed;
}

/* -----------------------------------------------------------------------------
 * Monitor field pairs - lengths and values.
 *
 * Note: we no longer pass number as the address of the number field separately,
 *       as we no longe support older version of epics base.
 */
static void monitor_field_pair (concatRecord * prec,
                                epicsUInt32 * number_field, void *value_field,
                                epicsUInt32 * mlast_number, void *mlast_value,
                                epicsUInt32 * alast_number, void *alast_value)
{
   const epicsUInt32 number = *number_field;
   unsigned short monitor_mask;
   unsigned short number_mask;
   unsigned short value_mask;
   bool changed;

   monitor_mask = recGblResetAlarms (prec);   /* DBE_ALARM if applicable ?? */

   number_mask = monitor_mask;
   value_mask = monitor_mask;

   /* Check for length and/or value changes since last monitor post.
    */
   if (*mlast_number != number) {

      /* When the number of elements changes then the value implicitly changes
       */
      *mlast_number = number;
      field_copy (mlast_value, value_field, number, prec->ftvl);

      number_mask |= DBE_VALUE;
      value_mask  |= DBE_VALUE;

   } else {

      /* When the number is the same, need only check the values.
       */
      changed = field_compare (mlast_value, value_field, number,
                               prec->ftvl, prec->mdel);
      if (changed) {
         field_copy (mlast_value, value_field, number, prec->ftvl);
         value_mask |= DBE_VALUE;
      }
   }

   /* Ditto last archive post.
    */
   if (*alast_number != number) {

      *alast_number = number;
      field_copy (alast_value, value_field, number, prec->ftvl);

      number_mask |= DBE_ARCHIVE;
      value_mask  |= DBE_ARCHIVE;

   } else {

      /* When the number is the same, need only check the values.
       */
      changed = field_compare (alast_value, value_field, number,
                               prec->ftvl, prec->adel);
      if (changed) {
         field_copy (alast_value, value_field, number, prec->ftvl);
         value_mask |= DBE_ARCHIVE;
      }
   }

   /* Now post the monitor and log (archive) events.
    */
   if (number_mask != 0) {
      db_post_events (prec, number_field, number_mask);
   }

   if (value_mask != 0) {
      db_post_events (prec, value_field, value_mask);
   }
}                               /* monitor_field_pair */

/* -----------------------------------------------------------------------------
 */
static void monitor (concatRecord * prec)
{
   concatPrivate *rpvt = (concatPrivate *) prec->rpvt;
   int j;

   /* Monitor the main VALue field and size.
    */
   monitor_field_pair (prec, &prec->nord, prec->val,
                       &rpvt->mlst.nord, rpvt->mlst.val,
                       &rpvt->alst.nord, rpvt->alst.val);

   /* Monitor the input arrays and sizes.
    */
   for (j = 0; j < NUM_ARGS; j++) {
      monitor_field_pair (prec, &(&prec->ne00)[j], (&prec->v00)[j],
                          &rpvt->mlst.inputNumber[j], rpvt->mlst.inputValues[j],
                          &rpvt->alst.inputNumber[j], rpvt->alst.inputValues[j]);
   }
}                               /* monitor */

/* -----------------------------------------------------------------------------
 */
static long cvt_dbaddr (DBADDR *paddr)
{
   concatRecord *prec = (concatRecord *) paddr->precord;
   const int fieldIndex = dbGetFieldIndex (paddr);

   if (fieldIndex == concatRecordVAL) {

      paddr->pfield = prec->val;
      paddr->no_elements = prec->nelm;
      paddr->field_type = prec->ftvl;
      paddr->dbr_field_type = paddr->field_type;
      paddr->field_size = dbValueSize (paddr->field_type);

   } else if (fieldIndex >= VFIRST && fieldIndex <= VLAST) {

      const int offset = fieldIndex - VFIRST;
      paddr->pfield = (&prec->v00)[offset];

      /* Must be at least 1 element.
       */
      paddr->no_elements = MAX (1, (&prec->me00)[offset]);
      paddr->field_type = prec->ftvl;
      paddr->dbr_field_type = paddr->field_type;
      paddr->field_size = dbValueSize (paddr->field_type);

   } else {
      concatError (prec, "cvt_dbaddr unexpectedly called for field %s",
                   ((dbFldDes *) paddr->pfldDes)->name);
   }

   return 0;
}                               /* cvt_dbaddr */


/* -----------------------------------------------------------------------------
 */
static long get_array_info (DBADDR* paddr, long* no_elements,
                            long* offset)
{
   concatRecord *prec = (concatRecord *) paddr->precord;
   const int fieldIndex = dbGetFieldIndex (paddr);

   if (fieldIndex == concatRecordVAL) {
      *no_elements = prec->nord;
   } else if (fieldIndex >= VFIRST && fieldIndex <= VLAST) {
      const int offset = fieldIndex - VFIRST;
      *no_elements = (&prec->ne00)[offset];
   } else {
      concatError (prec, "get_array_info unexpectedly called for field %s",
                   ((dbFldDes *) paddr->pfldDes)->name);
   }
   *offset = 0;

   return 0;
}                               /* get_array_info */


/* -----------------------------------------------------------------------------
 */
static long put_array_info (DBADDR *paddr, long nNew)
{
   concatRecord *prec = (concatRecord *) paddr->precord;
   const int fieldIndex = dbGetFieldIndex (paddr);

   if (fieldIndex == concatRecordVAL) {
      prec->nord = LIMIT (nNew, 1, prec->nelm);
   } else if (fieldIndex >= VFIRST && fieldIndex <= VLAST) {
      const int offset = fieldIndex - VFIRST;
      (&prec->ne00)[offset] = LIMIT (nNew, 1, (&prec->me00)[offset]);
   } else {
      concatError (prec, "put_array_info unexpectedly called for field %s",
                   ((dbFldDes *) paddr->pfldDes)->name);
   }
   return 0;
}                               /* put_array_info */

/* end */
