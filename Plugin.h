
#define GET_SELF_FROM_PPRIVATE(pprivate)        \
    re__engine__Plugin self;                    \
    SELF_FROM_PPRIVATE(self,pprivate);

/* re__engine__Plugin self; SELF_FROM_PPRIVATE(self,rx->pprivate) */
#define SELF_FROM_PPRIVATE(self, pprivate)                   \
	if (sv_isobject(pprivate)) {                             \
        SV * ref = SvRV((SV*)pprivate);                      \
	    IV tmp = SvIV((SV*)ref);                             \
	    self = INT2PTR(re__engine__Plugin,tmp);              \
    } else {                                                 \
        Perl_croak(aTHX_ "Not an object");                   \
    }

START_EXTERN_C
EXTERN_C const regexp_engine engine_plugin;
EXTERN_C REGEXP * Plugin_comp(pTHX_ const SV const *, const U32);
EXTERN_C I32      Plugin_exec(pTHX_ REGEXP * const, char *, char *,
                              char *, I32, SV *, void *, U32);
EXTERN_C char *   Plugin_intuit(pTHX_ REGEXP * const, SV *, char *,
                                char *, U32, re_scream_pos_data *);
EXTERN_C SV *     Plugin_checkstr(pTHX_ REGEXP * const);
EXTERN_C void     Plugin_free(pTHX_ REGEXP * const);
EXTERN_C void     Plugin_numbered_buff_FETCH(pTHX_ REGEXP * const,
                                             const I32, SV * const);
EXTERN_C void     Plugin_numbered_buff_STORE(pTHX_ REGEXP * const,
                                             const I32, SV const * const);
EXTERN_C I32      Plugin_numbered_buff_LENGTH(pTHX_ REGEXP * const,
                                              const SV * const, const I32);
EXTERN_C SV *     Plugin_named_buff_FETCH(pTHX_ REGEXP * const, SV * const,
                                          const U32);
EXTERN_C void     Plugin_named_buff_STORE(pTHX_ REGEXP * const rx,
                                          SV * const key, SV * const value,
                                          const U32 flags);
EXTERN_C void     Plugin_named_buff_DELETE(pTHX_ REGEXP * const rx,
                                           SV * const key, const U32 flags);
EXTERN_C void     Plugin_named_buff_CLEAR (pTHX_ REGEXP * const rx, const U32 flags);
EXTERN_C bool     Plugin_named_buff_EXISTS (pTHX_ REGEXP * const rx,
                                            SV * const key, const U32 flags);
EXTERN_C SV *     Plugin_named_buff_FIRSTKEY (pTHX_ REGEXP * const rx,
                                              const U32 flags);
EXTERN_C SV *     Plugin_named_buff_NEXTKEY (pTHX_ REGEXP * const rx,
                                             SV * const lastkey, const U32 flags);
EXTERN_C SV *     Plugin_named_buff_SCALAR (pTHX_ REGEXP * const rx,
                                            const U32 flags);
EXTERN_C SV *     Plugin_package(pTHX_ REGEXP * const);
#ifdef USE_ITHREADS
EXTERN_C void *   Plugin_dupe(pTHX_ REGEXP * const, CLONE_PARAMS *);
#endif
END_EXTERN_C

START_EXTERN_C
EXTERN_C const regexp_engine engine_plugin;
END_EXTERN_C

#define RE_ENGINE_PLUGIN (&engine_plugin)
const regexp_engine engine_plugin = {
    Plugin_comp,
    Plugin_exec,
    Plugin_intuit,
    Plugin_checkstr,
    Plugin_free,
    Plugin_numbered_buff_FETCH,
    Plugin_numbered_buff_STORE,
    Plugin_numbered_buff_LENGTH,
    Plugin_named_buff_FETCH,
    Plugin_named_buff_STORE,
    Plugin_named_buff_DELETE,
    Plugin_named_buff_CLEAR,
    Plugin_named_buff_EXISTS,
    Plugin_named_buff_FIRSTKEY,
    Plugin_named_buff_NEXTKEY,
    Plugin_named_buff_SCALAR,
    Plugin_package,
#if defined(USE_ITHREADS)        
    Plugin_dupe,
#endif
};

typedef struct replug {
    /* Pointer back to the containing REGEXP struct so that accessors
     * can modify nparens, gofs etc. */
    REGEXP * rx;

    /* A copy of the pattern given to comp, for ->pattern */
    SV * pattern;

    /* A copy of the string being matched against, for ->str */
    SV * str;

    /* The ->stash */
    SV * stash;

    /*
     * Callbacks
     */

    /* ->num_captures */
    SV * cb_num_capture_buff_FETCH;
    SV * cb_num_capture_buff_STORE;
    SV * cb_num_capture_buff_LENGTH;

    /* ->named_captures */
    SV * cb_named_capture_buff_FETCH;
    SV * cb_named_capture_buff_STORE;
    SV * cb_named_capture_buff_DELETE;
    SV * cb_named_capture_buff_CLEAR;
    SV * cb_named_capture_buff_EXISTS;
    SV * cb_named_capture_buff_FIRSTKEY;
    SV * cb_named_capture_buff_NEXTKEY;
    SV * cb_named_capture_buff_SCALAR;
} *re__engine__Plugin;