#lang rosette

(require (file "tables.rkt"))
(require "tdx_lib.rkt")
(require "cache_instance_hkid.rkt")

(displayln "=== Proof: Confidentiality Properties ===")

(define bv28 (bitvector 28))

;; GPAW constant (Guest Physical Address Width)
(define GPAW 48)
(define GPAW-limit (expt 2 GPAW))  ; 2^48

;; MKTME partition constants
(define NUM_HKID_KEYS     8)   ; last shared HKID index (0..8 = shared range)
(define NUM_TDX_PRIV_KIDS 56)  ; number of private HKIDs available
(define HKID_TME          0)   ; HKID=0 is always the legacy TME key
(define KEY_ZERO          0)   ; sentinel: zeroized / no key
 
;; Attestation-layer constants
(define SEAM_MODE_ACTIVE  1)   ; flag value: CPU is in SEAM mode
(define SEAM_MODULE_PRIV  2)   ; requester privilege level = TDX Module

;; L2 SEPT state constants (needed by cP24 and related properties)
(define L2_FREE     0)   ; L2 SEPT entry: not allocated
(define L2_MAPPED   1)   ; L2 SEPT entry: mapped and accessible
(define L2_BLOCKED  2)   ; L2 SEPT entry: blocked, not accessible

;; L2 profiling constants (needed by cP29)
(define PMT_PROF_DISABLED 0)   ; ATTRIBUTES.PMT_PROF = 0, profiling disabled
(define PMT_PROF_ENABLED  1)   ; ATTRIBUTES.PMT_PROF = 1, profiling enabled

;; DMA result constants (needed by cP32)
(define DMA_DENIED_OR_FAULT 0)   ; DMA access denied or caused integrity fault
(define DMA_SUCCEEDED       1)   ; DMA access succeeded
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Cache Confidentiality (Base property)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic pa1 bv28)
(define-symbolic repl-way integer?)
(define-symbolic hkid1 hkid2 integer?)

(define-values (hit1 way1 data1) (query-cache pa1 repl-way hkid1))
(define-values (hit2 way2 data2) (query-cache pa1 repl-way hkid2))

(define confidentiality-assertion
  (assert (not (and hit1 hit2
                    (not (= hkid1 hkid2))))))  ; dono hit + alag HKID — IMPOSSIBLE

(define result (verify confidentiality-assertion))
(displayln (if (unsat? result)
               "Base Cache Confidentiality VERIFIED"
               "Base Cache Confidentiality VIOLATED"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP1: GPA->HPA mapping unique hona chahiye (no aliasing)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hpa-c1a hpa-c1b integer?)
(define-symbolic gpa-c1a gpa-c1b integer?)
(define-symbolic state-c1a state-c1b integer?)

(define entry1 (make-secure_EPT_entry hpa-c1a gpa-c1a state-c1a))
(define entry2 (make-secure_EPT_entry hpa-c1b gpa-c1b state-c1b))

(define cP1
  (assert (not (and (secure_EPT_entry? entry1)
                    (secure_EPT_entry? entry2)
                    (= (secure_EPT_entry-host_physical_address entry1)
                       (secure_EPT_entry-host_physical_address entry2))
                    (not (= gpa-c1a gpa-c1b))))))
                    ; same HPA + alag GPA — IMPOSSIBLE

(define result-cP1 (verify cP1))
(displayln (if (unsat? result-cP1)
               "cP1 VERIFIED: GPA->HPA mappings are unique (no aliasing)"
               "cP1 VIOLATED: GPA->HPA aliasing detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP2: HKID encryption keys KET se leak nahi hone chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hkid-c2a hkid-c2b integer?)
(define ket1 (hash-ref KET hkid-c2a #f))
(define ket2 (hash-ref KET hkid-c2b #f))

(define cP2
  (assert (not (and ket1
                    ket2
                    (not (= hkid-c2a hkid-c2b))
                    (= ket1 ket2)))))
                    ; alag HKID + same key — IMPOSSIBLE

(define result-cP2 (verify cP2))
(displayln (if (unsat? result-cP2)
               "cP2 VERIFIED: HKID encryption keys are not leaked"
               "cP2 VIOLATED: HKID encryption key leak detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP3: KOT mein HKID state confidential hona chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hkid3 hkid4 integer?)
(define kot1 (hash-ref KOT hkid3 #f))
(define kot2 (hash-ref KOT hkid4 #f))

(define cP3
  (assert (not (and kot1
                    kot2
                    (not (= hkid3 hkid4))
                    (= kot1 kot2)))))
                    ; alag HKID + same state — IMPOSSIBLE

(define result-cP3 (verify cP3))
(displayln (if (unsat? result-cP3)
               "cP3 VERIFIED: HKID assignment state in KOT is confidential"
               "cP3 VIOLATED: HKID assignment state leak detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP4: TDR lifecycle state confidential hona chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic lstate-c4a lstate-c4b integer?)
(define-symbolic hkid-c4a hkid-c4b integer?)

(define tdr1 (make-TDR #f #f 0 0 0 lstate-c4a hkid-c4a 0 #f #f))
(define tdr2 (make-TDR #f #f 0 0 0 lstate-c4b hkid-c4b 0 #f #f))

(define cP4
  (assert (not (and (TDR? tdr1)
                    (TDR? tdr2)
                    (not (= (TDR-HKID tdr1) (TDR-HKID tdr2)))
                    (= (TDR-LIFECYCLE_STATE tdr1)
                       (TDR-LIFECYCLE_STATE tdr2))))))
                    ; alag HKID + same lifecycle — IMPOSSIBLE

(define result-cP4 (verify cP4))
(displayln (if (unsat? result-cP4)
               "cP4 VERIFIED: TDR lifecycle state is confidential"
               "cP4 VIOLATED: TDR lifecycle state leak detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP5: EPT page states confidential hona chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hpa-c5a hpa-c5b integer?)
(define-symbolic gpa-c5a gpa-c5b integer?)
(define-symbolic state-c5a state-c5b integer?)

(define pg-entry1 (make-secure_EPT_entry hpa-c5a gpa-c5a state-c5a))
(define pg-entry2 (make-secure_EPT_entry hpa-c5b gpa-c5b state-c5b))

(define cP5
  (assert (not (and (secure_EPT_entry? pg-entry1)
                    (secure_EPT_entry? pg-entry2)
                    (not (= gpa-c5a gpa-c5b))
                    (= (secure_EPT_entry-state pg-entry1)
                       (secure_EPT_entry-state pg-entry2))))))
                    ; alag GPA + same state — IMPOSSIBLE

(define result-cP5 (verify cP5))
(displayln (if (unsat? result-cP5)
               "cP5 VERIFIED: Page states in secure EPT are confidential"
               "cP5 VIOLATED: EPT page state leak detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP6: HKID key config state confidential hona chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pa-c6 400000)
(define hkid-c6 7)

(hash-set! PAMT pa-c6 (make-PAMT_entry PT_NDA 0 0))
(hash-set! KOT  hkid-c6 HKID_FREE)

(define tdr3-raw (TDH_MNG_CREATE pa-c6 hkid-c6))

(when (TDR? tdr3-raw)
  (hash-set! PAMT pa-c6 (make-PAMT_entry PT_TDR 0 0)))

(define configured-tdr
  (if (TDR? tdr3-raw)
      (TDH_MNG_KEY_CONFIG pa-c6 tdr3-raw)
      #f))

(define cP6
  (assert (not (and (TDR? configured-tdr)
                    (not (= (TDR-HKID tdr3-raw) 99))
                    (= (TDR-LIFECYCLE_STATE configured-tdr)
                       (hash-ref KOT 99 #f))))))
                    ; configured TDR + attacker state match — IMPOSSIBLE

(define result-cP6 (verify cP6))
(displayln (if (unsat? result-cP6)
               "cP6 VERIFIED: Key configuration state of HKID is confidential"
               "cP6 VIOLATED: Key configuration state leak detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP7: TDR finalization status confidential hona chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pa-c7 500000)
(define hkid-c7 8)

(hash-set! PAMT pa-c7 (make-PAMT_entry PT_NDA 0 0))
(hash-set! KOT  hkid-c7 HKID_FREE)

(define tdr4-raw (TDH_MNG_CREATE pa-c7 hkid-c7))

(when (TDR? tdr4-raw)
  (hash-set! PAMT pa-c7 (make-PAMT_entry PT_TDR 0 0)))

(define tdr4-keyed
  (if (TDR? tdr4-raw)
      (TDH_MNG_KEY_CONFIG pa-c7 tdr4-raw)
      #f))

(define tdr4-inited
  (if (TDR? tdr4-keyed)
      (TDH_MNG_INIT pa-c7 tdr4-keyed)
      #f))

(define finalized-tdr
  (if (TDR? tdr4-inited)
      (TDH_MNG_FINALIZE pa-c7 tdr4-inited)
      #f))

(define cP7
  (assert (not (and (TDR? finalized-tdr)
                    (not (= (TDR-HKID finalized-tdr) 88))
                    (= (TDR-FINALIZED finalized-tdr)
                       (TDR-FINALIZED tdr4-raw))))))
                    ; finalized + attacker same state — IMPOSSIBLE

(define result-cP7 (verify cP7))
(displayln (if (unsat? result-cP7)
               "cP7 VERIFIED: Finalization status of TDCS is confidential"
               "cP7 VIOLATED: Finalization status leak detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP8: EPT shared bit confidential hona chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hpa-c8a hpa-c8b integer?)
(define-symbolic shared-c8a shared-c8b integer?)
(define-symbolic state-c8a state-c8b integer?)
(define-symbolic gpa-c8a gpa-c8b integer?)

(define entry5 (make-secure_EPT_entry hpa-c8a shared-c8a state-c8a))
(define entry6 (make-secure_EPT_entry hpa-c8b shared-c8b state-c8b))

(define cP8
  (assert (not (and (secure_EPT_entry? entry5)
                    (secure_EPT_entry? entry6)
                    (not (= gpa-c8a gpa-c8b))
                    (= (secure_EPT_entry-GPA_SHARED entry5)
                       (secure_EPT_entry-GPA_SHARED entry6))))))
                    ; alag GPA + same shared bit — IMPOSSIBLE

(define result-cP8 (verify cP8))
(displayln (if (unsat? result-cP8)
               "cP8 VERIFIED: Shared bit status in EPT entries is confidential"
               "cP8 VIOLATED: Shared bit status leak detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP9: TDR package config bitmap confidential hona chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic pkg-c9a pkg-c9b integer?)
(define-symbolic hkid-c9a hkid-c9b integer?)
(define-symbolic lstate-c9a lstate-c9b integer?)

(define tdr5 (make-TDR #f #f 0 0 0 lstate-c9a hkid-c9a pkg-c9a #f #f))
(define tdr6 (make-TDR #f #f 0 0 0 lstate-c9b hkid-c9b pkg-c9b #f #f))

(define cP9
  (assert (not (and (TDR? tdr5)
                    (TDR? tdr6)
                    (not (= (TDR-HKID tdr5) (TDR-HKID tdr6)))
                    (= (TDR-PKG_CONFIG_BITMAP tdr5)
                       (TDR-PKG_CONFIG_BITMAP tdr6))))))
                    ; alag HKID + same bitmap — IMPOSSIBLE

(define result-cP9 (verify cP9))
(displayln (if (unsat? result-cP9)
               "cP9 VERIFIED: Package configuration bitmap in TDR is confidential"
               "cP9 VIOLATED: Package config bitmap leak detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP10: VCPU → HKID association confidential hona chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hkid-v1 hkid-v2 integer?)
(define tdvps1 (make-TDVPS 0 #t 0 0 0 0 hkid-v1 0 0))
(define tdvps2 (make-TDVPS 0 #t 1 0 0 0 hkid-v2 0 0))

(define cP10
  (assert (not (and (not (= (TDVPS-VCPU_INDEX tdvps1)
                            (TDVPS-VCPU_INDEX tdvps2)))
                    (= (TDVPS-ASSOC_HKID tdvps1)
                       (TDVPS-ASSOC_HKID tdvps2))))))
                    ; alag VCPU + same HKID — IMPOSSIBLE

(define result-cP10 (verify cP10))
(displayln (if (unsat? result-cP10)
               "cP10 VERIFIED: VCPU to HKID association is confidential"
               "cP10 VIOLATED: VCPU->HKID association leak detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP11: L2_GPA_ALIAS_PROT (Nested Privacy)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic l2-gpa-c11      integer?)
(define-symbolic l2-hpa-c11      integer?)
(define-symbolic l1-priv-hpa-c11 integer?)
(define-symbolic l1-priv-flag-c11 boolean?)  ; #t = L1 private HPA hai

(define cP11
  (assert
    (not (and l1-priv-flag-c11
              (= l2-hpa-c11 l1-priv-hpa-c11)))))
              ; L2 translation ne L1 private HPA ko alias kiya — IMPOSSIBLE

(define result-cP11 (verify cP11))
(displayln (if (unsat? result-cP11)
               "cP11 VERIFIED: L2_GPA_ALIAS_PROT - L2 Guest cannot alias L1 private memory"
               "cP11 VIOLATED: L2_GPA_ALIAS_PROT - L2 Guest aliased L1 private HPA"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP40: SEPT_ZERO_INIT (Memory Scrubbing)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic td-owner-c40 boolean?)
(define-symbolic hkid-c40 integer?)
(define-symbolic mac-c40 integer?)

(define new-page-c40
  (make-cache_entry td-owner-c40 hkid-c40 mac-c40 0))  ; DATA=0 zero-init

(define cP40
  (assert
    (not (and (cache_entry? new-page-c40)
              (not (= (cache_entry-DATA new-page-c40) 0))))))
              ; valid entry + non-zero data — IMPOSSIBLE

(define result-cP40 (verify cP40))
(displayln (if (unsat? result-cP40)
               "cP40 VERIFIED: SEPT_ZERO_INIT - Pages are zero-initialized before SEPT assignment"
               "cP40 VIOLATED: SEPT_ZERO_INIT - Residual data found in new SEPT page"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP41: GPA_WIDTH_CHECK (Boundary Enforcement)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic gpa-c41   integer?)
(define-symbolic hpa-c41   integer?)
(define-symbolic state-c41 integer?)

(define sept-c41
  (make-secure_EPT_entry hpa-c41 gpa-c41 state-c41))

(define cP41
  (assert
    (not (and (secure_EPT_entry? sept-c41)
              (= (secure_EPT_entry-state sept-c41) SEPT_PRESENT)
              (>= gpa-c41 GPAW-limit)))))
              ; PRESENT entry + GPA out of bounds — IMPOSSIBLE

(define result-cP41 (verify cP41))
(displayln (if (unsat? result-cP41)
               "cP41 VERIFIED: GPA_WIDTH_CHECK - All GPA accesses within GPAW bounds"
               "cP41 VIOLATED: GPA_WIDTH_CHECK - Out-of-bounds GPA access detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP42: XD_BIT_STRICT (Execution Control Enforcement)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic xd-bit-c42       boolean?)
(define-symbolic exec-attempt-c42 boolean?)

(define cP42
  (assert
    (not (and xd-bit-c42
              exec-attempt-c42))))
              ; XD set + execution — IMPOSSIBLE

(define result-cP42 (verify cP42))
(displayln (if (unsat? result-cP42)
               "cP42 VERIFIED: XD_BIT_STRICT - XD pages cannot be executed"
               "cP42 VIOLATED: XD_BIT_STRICT - Execution on XD page detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP43: TDCS_OPAQUE_METADATA (Opaque Control)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic guest-read-c43    boolean?)
(define-symbolic tdcs-visible-c43  boolean?)

(define cP43
  (assert
    (not (and tdcs-visible-c43
              guest-read-c43))))
              ; TDCS visible + guest read — IMPOSSIBLE

(define result-cP43 (verify cP43))
(displayln (if (unsat? result-cP43)
               "cP43 VERIFIED: TDCS_OPAQUE_METADATA - TDCS internal data is opaque to Guest VM"
               "cP43 VIOLATED: TDCS_OPAQUE_METADATA - Guest VM accessed TDCS internal metadata"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP44: SHARED_BIT_INVARIANCE (No Mid-Walk Flipping)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic shared-bit-start-c44  integer?)
(define-symbolic shared-bit-end-c44    integer?)
(define-symbolic walk-in-progress-c44  boolean?)

(define cP44
  (assert
    (not (and walk-in-progress-c44
              (not (= shared-bit-start-c44
                      shared-bit-end-c44))))))
              ; shared bit changed during walk — IMPOSSIBLE

(define result-cP44 (verify cP44))
(displayln (if (unsat? result-cP44)
               "cP44 VERIFIED: SHARED_BIT_INVARIANCE - Shared bit stable during SEPT walk"
               "cP44 VIOLATED: SHARED_BIT_INVARIANCE - Shared bit flipped mid-walk detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP45: TRACE_EXCLUSION_LOCK (Debug Isolation)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic pt-write-addr-c45  integer?)
(define-symbolic td-priv-start-c45  integer?)
(define-symbolic td-priv-end-c45    integer?)
(define-symbolic pt-active-c45      boolean?)

(define cP45
  (assert
    (not (and pt-active-c45
              (>= pt-write-addr-c45 td-priv-start-c45)
              (< pt-write-addr-c45 td-priv-end-c45)))))
              ; PT active + write inside private range — IMPOSSIBLE

(define result-cP45 (verify cP45))
(displayln (if (unsat? result-cP45)
               "cP45 VERIFIED: TRACE_EXCLUSION_LOCK - PT output cannot write to TD-private memory"
               "cP45 VIOLATED: TRACE_EXCLUSION_LOCK - PT output written to TD-private memory"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; NEW MKTME CONFIDENTIALITY PROPERTIES
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP12: MKTME_KEY_ISOLATION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hkid-cm1-A  integer?)   ; HKID assigned to TD-A
(define-symbolic hkid-cm1-B  integer?)   ; HKID assigned to TD-B
(define-symbolic key-cm1-A   integer?)   ; KET key entry for hkid-cm1-A
(define-symbolic key-cm1-B   integer?)   ; KET key entry for hkid-cm1-B

;; Populate KET with distinct symbolic keys
(hash-set! KET hkid-cm1-A key-cm1-A)
(hash-set! KET hkid-cm1-B key-cm1-B)

(define cM1
  (assert
    (not (and (not (= hkid-cm1-A hkid-cm1-B))    ; different TDs (different HKIDs)
              (> key-cm1-A KEY_ZERO)               ; TD-A has a real key
              (> key-cm1-B KEY_ZERO)               ; TD-B has a real key
              (= (hash-ref KET hkid-cm1-A #f)
                 (hash-ref KET hkid-cm1-B #f)))))) ; same key — IMPOSSIBLE

(define result-cM1 (verify cM1))
(displayln (if (unsat? result-cM1)
               "cP12 VERIFIED: MKTME_KEY_ISOLATION - Different TDs hold distinct KET keys"
               "cP12 VIOLATED: MKTME_KEY_ISOLATION - Two TDs share the same encryption key"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP13: MKTME_CIPHERTEXT_UNIQUENESS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic plaintext-cm2   integer?)   ; same plaintext value
(define-symbolic hkid-cm2-X      integer?)   ; HKID for TD-X
(define-symbolic hkid-cm2-Y      integer?)   ; HKID for TD-Y
(define-symbolic cipher-cm2-X    integer?)   ; ciphertext produced by HKID-X
(define-symbolic cipher-cm2-Y    integer?)   ; ciphertext produced by HKID-Y

;; Keys in KET must be distinct (guaranteed by cM1 above)
(define-symbolic key-cm2-X key-cm2-Y integer?)
(hash-set! KET hkid-cm2-X key-cm2-X)
(hash-set! KET hkid-cm2-Y key-cm2-Y)

(define cM2
  (assert
    (not (and (not (= hkid-cm2-X hkid-cm2-Y))       ; different HKIDs
              (not (= key-cm2-X  key-cm2-Y))          ; different keys (from cM1)
              (= plaintext-cm2   plaintext-cm2)        ; same plaintext (trivially true)
              (= cipher-cm2-X    cipher-cm2-Y)))))     ; same ciphertext — IMPOSSIBLE

(define result-cM2 (verify cM2))
(displayln (if (unsat? result-cM2)
               "cP13 VERIFIED: MKTME_CIPHERTEXT_UNIQUENESS - Different HKIDs produce distinct ciphertext"
               "cP13 VIOLATED: MKTME_CIPHERTEXT_UNIQUENESS - Ciphertext collision across HKIDs detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP14: MKTME_PRIVATE_HKID_SEAM_ONLY
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hkid-cm3       integer?)    ; HKID under test
(define-symbolic seam-mode-cm3  boolean?)    ; #t = CPU in SEAM mode
(define-symbolic access-ok-cm3  boolean?)    ; did read return real data?

(define cM3
  (assert
    (not (and (> hkid-cm3 NUM_HKID_KEYS)     ; private HKID range (> shared boundary)
              (not seam-mode-cm3)             ; CPU is NOT in SEAM mode
              access-ok-cm3))))               ; access returned real data — IMPOSSIBLE

(define result-cM3 (verify cM3))
(displayln (if (unsat? result-cM3)
               "cP14 VERIFIED: MKTME_PRIVATE_HKID_SEAM_ONLY - Private HKID accessible in SEAM mode only"
               "cP14 VIOLATED: MKTME_PRIVATE_HKID_SEAM_ONLY - Non-SEAM access with private HKID succeeded"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP15: MKTME_ZERO_HKID_TME
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic assigned-hkid-cm4   integer?)   ; HKID given to a new TD
(define-symbolic td-created-cm4      boolean?)   ; TDH.MNG.CREATE succeeded?

(define cM4
  (assert
    (not (and (= assigned-hkid-cm4 HKID_TME)    ; HKID=0 attempted
              td-created-cm4))))                  ; TD creation succeeded — IMPOSSIBLE

(define result-cM4 (verify cM4))
(displayln (if (unsat? result-cM4)
               "cP15 VERIFIED: MKTME_ZERO_HKID_TME - HKID=0 (TME key) never assigned to any TD"
               "cP15 VIOLATED: MKTME_ZERO_HKID_TME - TD created with HKID=0 (TME key) detected"))

 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ATTESTATION CONFIDENTIALITY PROPERTIES
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP16: ASRT_REPORTDATA_BINDING
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic reportdata-guest-cA1  integer?)  ; value guest passed to TDG.MR.REPORT
(define-symbolic reportdata-report-cA1 integer?)  ; value written into TDREPORT_STRUCT
(define-symbolic report-generated-cA1  boolean?)  ; TDG.MR.REPORT completed successfully
 
(define cA1
  (assert
    (not (and report-generated-cA1               ; report was successfully generated
              (not (= reportdata-guest-cA1
                      reportdata-report-cA1))))))  ; input ≠ stored value — IMPOSSIBLE
 
(define result-cA1 (verify cA1))
(displayln (if (unsat? result-cA1)
               "cP16 VERIFIED: ASRT_REPORTDATA_BINDING - REPORTDATA in TDREPORT exactly matches guest input"
               "cP16 VIOLATED: ASRT_REPORTDATA_BINDING - REPORTDATA mismatch detected in TDREPORT"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP17: ASRT_REPORT_KEY_ISOLATION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic td-uuid-cA2-X   integer?)  ; TD-X universally unique identifier
(define-symbolic td-uuid-cA2-Y   integer?)  ; TD-Y universally unique identifier
(define-symbolic report-key-cA2-X integer?) ; REPORT_KEY derived for TD-X
(define-symbolic report-key-cA2-Y integer?) ; REPORT_KEY derived for TD-Y
 
(define cA2
  (assert
    (not (and (not (= td-uuid-cA2-X td-uuid-cA2-Y))   ; TDs have different UUIDs
              (not (= report-key-cA2-X 0))              ; X has a non-null key
              (not (= report-key-cA2-Y 0))              ; Y has a non-null key
              (= report-key-cA2-X report-key-cA2-Y))))) ; same REPORT_KEY — IMPOSSIBLE
 
(define result-cA2 (verify cA2))
(displayln (if (unsat? result-cA2)
               "cP17 VERIFIED: ASRT_REPORT_KEY_ISOLATION - Each TD holds a unique REPORT_KEY"
               "cP17 VIOLATED: ASRT_REPORT_KEY_ISOLATION - Two distinct TDs share the same REPORT_KEY"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP18: ASRT_MAC_KEY_PROTECTION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic seam-mode-cA3      integer?)  ; 1 = in SEAM mode, 0 = not in SEAM mode
(define-symbolic mac-key-read-cA3   boolean?)  ; attempt to read SEAM_REPORT_KEY succeeded?
(define-symbolic requester-priv-cA3 integer?)  ; 0=guest, 1=VMM, 2=SEAM_MODULE
 
;; Only SEAM_MODULE (priv=2) while seam-mode=1 may succeed in reading the key
(define cA3
  (assert
    (not (and mac-key-read-cA3                            ; key read succeeded
              (or (not (= seam-mode-cA3 SEAM_MODE_ACTIVE))   ; NOT in SEAM mode
                  (not (= requester-priv-cA3 SEAM_MODULE_PRIV)))))))
              ; read succeeded by non-module or outside SEAM mode — IMPOSSIBLE
 
(define result-cA3 (verify cA3))
(displayln (if (unsat? result-cA3)
               "cP18 VERIFIED: ASRT_MAC_KEY_PROTECTION - SEAM_REPORT_KEY accessible only inside SEAM module"
               "cP18 VIOLATED: ASRT_MAC_KEY_PROTECTION - Root MAC key exposed outside SEAM module"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP19: ASRT_ATTRIBUTES_FIDELITY
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic tdcs-attributes-cA4   integer?)  ; actual ATTRIBUTES in TDCS
(define-symbolic report-attributes-cA4 integer?)  ; ATTRIBUTES written into TDREPORT_STRUCT
(define-symbolic report-issued-cA4     boolean?)  ; TDG.MR.REPORT completed successfully
 
(define cA4
  (assert
    (not (and report-issued-cA4                       ; report was successfully issued
              (not (= tdcs-attributes-cA4
                      report-attributes-cA4))))))      ; field mismatch — IMPOSSIBLE
 
(define result-cA4 (verify cA4))
(displayln (if (unsat? result-cA4)
               "cP19 VERIFIED: ASRT_ATTRIBUTES_FIDELITY - TDREPORT.ATTRIBUTES matches TDCS.ATTRIBUTES exactly"
               "cP19 VIOLATED: ASRT_ATTRIBUTES_FIDELITY - ATTRIBUTES mismatch in TDREPORT detected"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP20: ASRT_SERVTD_BINDING
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic servtd-hash-tdcs-cA5   integer?)  ; SERVTD_HASH computed and stored in TDCS
(define-symbolic servtd-hash-report-cA5 integer?)  ; SERVTD_HASH written into TDREPORT_STRUCT
(define-symbolic servtd-bound-cA5       boolean?)  ; at least one service TD is bound
(define-symbolic report-issued-cA5      boolean?)  ; TDG.MR.REPORT completed successfully
 
(define cA5
  (assert
    (not (and report-issued-cA5                          ; report was successfully issued
              servtd-bound-cA5                            ; a service TD is bound
              (not (= servtd-hash-tdcs-cA5
                      servtd-hash-report-cA5))))))        ; hash mismatch — IMPOSSIBLE
 
(define result-cA5 (verify cA5))
(displayln (if (unsat? result-cA5)
               "cp20 VERIFIED: ASRT_SERVTD_BINDING - SERVTD_HASH in TDREPORT matches TDCS binding table"
               "cP20 VIOLATED: ASRT_SERVTD_BINDING - SERVTD_HASH tampered between TDCS and TDREPORT"))
 



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; L1/L2 Manual  TD PARTITIONING CONFIDENTIALITY PROPERTIES  [NEW]
;;
;; Mapping:
;;   Doc P1  -> cP21  L2_SEPT_ALIAS_COLLISION
;;   Doc P5  -> cP22  L2_VMID_HKID_BINDING
;;   Doc P6  -> cP23  L2_ASID_TLB_FLUSH_ON_SWITCH
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; L1/L2 constants
(define L2_VM_C           2)   ; CURR_VM value for L2 Guest


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP21: L2_SEPT_ALIAS_COLLISION  [Doc P1]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic l2-vmid-A-cp21 l2-vmid-B-cp21 integer?)  ; two L2 VM identifiers
(define-symbolic l2-hpa-A-cp21  l2-hpa-B-cp21  integer?)  ; their SEPT target HPAs
(define-symbolic alias-allowed-cp21 boolean?)  ; L1 VMM ne explicitly allow kiya

(define cP21
  (assert
    (not (and (not (= l2-vmid-A-cp21 l2-vmid-B-cp21))  ; alag L2 VMs
              (= l2-hpa-A-cp21 l2-hpa-B-cp21)           ; same HPA share
              (not alias-allowed-cp21)))))               ; L1 ne allow nahi kiya — IMPOSSIBLE

(define result-cP21 (verify cP21))
(displayln (if (unsat? result-cP21)
               "cP21 VERIFIED: L2_SEPT_ALIAS_COLLISION - No unauthorized cross-L2 HPA aliasing"
               "cP21 VIOLATED: L2_SEPT_ALIAS_COLLISION - Two L2 VMs share HPA without L1 permission"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP22: L2_VMID_HKID_BINDING  [Doc P5]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic l2-alias-hkid-cp22  integer?)  ; HKID jo L2 alias entry use kar rahi
(define-symbolic td-parent-hkid-cp22 integer?)  ; parent TD ka assigned HKID (from TDR)
(define-symbolic l2-alias-valid-cp22 boolean?)  ; L2 SEPT alias entry valid/present

(define cP22
  (assert
    (not (and l2-alias-valid-cp22
              (not (= l2-alias-hkid-cp22
                      td-parent-hkid-cp22))))))  ; valid alias + wrong HKID — IMPOSSIBLE

(define result-cP22 (verify cP22))
(displayln (if (unsat? result-cP22)
               "cP22 VERIFIED: L2_VMID_HKID_BINDING - L2 aliased pages always use parent TD HKID"
               "cP22 VIOLATED: L2_VMID_HKID_BINDING - L2 alias uses wrong HKID; KeyID spoofing detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP23: L2_ASID_TLB_FLUSH_ON_SWITCH  [Doc P6]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic prev-l2-vmid-cp23 curr-l2-vmid-cp23 integer?)  ; L2 VMID before/after switch
(define-symbolic tlb-flushed-cp23  boolean?)  ; TLB flush ya ASID invalidation hua
(define-symbolic stale-hit-cp23    boolean?)  ; current L2 ne pichle L2 ki TLB entry hit ki

(define cP23
  (assert
    (not (and (not (= prev-l2-vmid-cp23 curr-l2-vmid-cp23))  ; L2 switch hua
              (not tlb-flushed-cp23)                          ; TLB flush nahi hua
              stale-hit-cp23))))                               ; stale TLB hit — IMPOSSIBLE

(define result-cP23 (verify cP23))
(displayln (if (unsat? result-cP23)
               "cP23 VERIFIED: L2_ASID_TLB_FLUSH_ON_SWITCH - TLB flushed on every L2 VMID switch"
               "cP23 VIOLATED: L2_ASID_TLB_FLUSH_ON_SWITCH - Stale TLB from prev L2 hit; cross-L2 data leak"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ADDITIONAL L1/L2 TD PARTITIONING CONFIDENTIALITY PROPERTIES generated by Poperty engine  [NEW]
;;
;; Mapping:
;;   tpP3  -> cP24  L2_BLOCKED_NO_DATA_ACCESS
;;   tpP5  -> cP25  L2_TRANSLATION_CACHE_TAGGING
;;   tpP9  -> cP26  L2_HOST_EXIT_INFO_SANITIZED
;;   tpP11 -> cP27  L2_SHARED_BIT_TRANSLATION_CONSISTENCY
;;   tpP15 -> cP28  PAGING_CACHE_CROSS_TD_CONFIDENTIALITY
;;   tpP18 -> cP29  L2_PROFILING_ISOLATION
;;   tpP20 -> cP30  SPECULATIVE_L2_WALK_CHECK_BEFORE_FORWARD
;;   tpP24 -> cP31  L1_PRIVATE_STATE_NOT_LIVE_ACROSS_L2_ENTRY
;;   tpP25 -> cP32  HOST_DMA_BLOCKED_ON_L2_PRIVATE_ALIAS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP24: L2_BLOCKED_NO_DATA_ACCESS  [tpP3]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic l2-sept-state-cp24  integer?)  ; L2 SEPT entry state
(define-symbolic data-returned-cp24  boolean?)  ; data returned to L2
(define-symbolic cache-filled-cp24   boolean?)  ; cache fill occurred
(define-symbolic store-committed-cp24 boolean?) ; store committed
(define-symbolic fetch-retired-cp24  boolean?)  ; instruction fetch retired

(define cP24
  (assert
    (not (and (= l2-sept-state-cp24 L2_BLOCKED)
              (or data-returned-cp24
                  cache-filled-cp24
                  store-committed-cp24
                  fetch-retired-cp24)))))
              ; L2_BLOCKED + any data-producing effect — IMPOSSIBLE

(define result-cP24 (verify cP24))
(displayln (if (unsat? result-cP24)
               "cP24 VERIFIED: L2_BLOCKED_NO_DATA_ACCESS - L2_BLOCKED aliases produce no architectural/microarch data access"
               "cP24 VIOLATED: L2_BLOCKED_NO_DATA_ACCESS - L2_BLOCKED alias produced a data/cache/fetch effect"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP25: L2_TRANSLATION_CACHE_TAGGING  [tpP5]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic tlb-hit-cp25         boolean?)  ; TLB/paging-cache hit occurred
(define-symbolic tag-tdr-cp25         integer?)  ; cached entry's TDR tag
(define-symbolic current-tdr-cp25     integer?)  ; current TDR
(define-symbolic tag-hkid-cp25        integer?)  ; cached entry's HKID tag
(define-symbolic current-hkid-cp25    integer?)  ; current HKID
(define-symbolic tag-l2vmid-cp25      integer?)  ; cached entry's L2 VM ID tag
(define-symbolic current-l2vmid-cp25  integer?)  ; current L2 VM ID
(define-symbolic tag-septroot-cp25    integer?)  ; cached entry's SEPT root tag
(define-symbolic current-septroot-cp25 integer?) ; current SEPT root

(define cP25
  (assert
    (not (and tlb-hit-cp25
              (or (not (= tag-tdr-cp25 current-tdr-cp25))
                  (not (= tag-hkid-cp25 current-hkid-cp25))
                  (not (= tag-l2vmid-cp25 current-l2vmid-cp25))
                  (not (= tag-septroot-cp25 current-septroot-cp25)))))))
              ; TLB hit + any tag mismatch — IMPOSSIBLE

(define result-cP25 (verify cP25))
(displayln (if (unsat? result-cP25)
               "cP25 VERIFIED: L2_TRANSLATION_CACHE_TAGGING - TLB/paging-cache hits always match TDR/HKID/L2VM/SEPT_ROOT"
               "cP25 VIOLATED: L2_TRANSLATION_CACHE_TAGGING - TLB hit with mismatched TD/HKID/L2VM/SEPT_ROOT tag"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP26: L2_HOST_EXIT_INFO_SANITIZED  [tpP9]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic l2-exit-to-host-cp26     boolean?)  ; L2-originated exit reached host VMM
(define-symbolic host-info-has-priv-reg-cp26 boolean?)  ; private register value present
(define-symbolic host-info-has-priv-gpa-cp26 boolean?)  ; private GPA present (not explicitly allowed)
(define-symbolic host-info-has-priv-hpa-cp26 boolean?)  ; SEPT-derived private HPA present
(define-symbolic host-info-has-hkid-cp26     boolean?)  ; HKID value present
(define-symbolic host-info-has-td-meta-cp26  boolean?)  ; TD-internal metadata present

(define cP26
  (assert
    (not (and l2-exit-to-host-cp26
              (or host-info-has-priv-reg-cp26
                  host-info-has-priv-gpa-cp26
                  host-info-has-priv-hpa-cp26
                  host-info-has-hkid-cp26
                  host-info-has-td-meta-cp26)))))
              ; L2 exit to host + any private field present — IMPOSSIBLE

(define result-cP26 (verify cP26))
(displayln (if (unsat? result-cP26)
               "cP26 VERIFIED: L2_HOST_EXIT_INFO_SANITIZED - Host-visible L2 exit info excludes private TD/L1/L2 state"
               "cP26 VIOLATED: L2_HOST_EXIT_INFO_SANITIZED - Host-visible L2 exit info leaked private TD/L1/L2 state"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP27: L2_SHARED_BIT_TRANSLATION_CONSISTENCY  [tpP11]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic private-l2-access-cp27   boolean?)  ; L2 access classified private
(define-symbolic shared-l2-access-cp27    boolean?)  ; L2 access classified shared
(define-symbolic txn-hkid-cp27            integer?)  ; HKID used in the transaction
(define-symbolic td-private-hkid-cp27     integer?)  ; TD's private HKID
(define-symbolic td-owner-required-cp27   boolean?)  ; TD Owner required for this access
(define-symbolic td-owner-set-cp27        boolean?)  ; TD Owner actually set
(define-symbolic hkid-in-shared-range-cp27 boolean?) ; txn HKID is in shared HKID range
(define-symbolic private-sept-consumed-cp27 boolean?) ; a private SEPT leaf was consumed

(define cP27
  (assert
    (not (or
      ;; private access + (wrong HKID OR TD_OWNER not as required) — IMPOSSIBLE
      (and private-l2-access-cp27
           (or (not (= txn-hkid-cp27 td-private-hkid-cp27))
               (not (= td-owner-required-cp27 td-owner-set-cp27))))
      ;; shared access + (HKID not in shared range OR private SEPT leaf consumed) — IMPOSSIBLE
      (and shared-l2-access-cp27
           (or (not hkid-in-shared-range-cp27)
               private-sept-consumed-cp27))))))

(define result-cP27 (verify cP27))
(displayln (if (unsat? result-cP27)
               "cP27 VERIFIED: L2_SHARED_BIT_TRANSLATION_CONSISTENCY - Shared/private classification consistent across L1/L2"
               "cP27 VIOLATED: L2_SHARED_BIT_TRANSLATION_CONSISTENCY - Shared/private confused-deputy conversion detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP28: PAGING_CACHE_CROSS_TD_CONFIDENTIALITY  [tpP15]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic pwc-entry-tdr-cp28        integer?)  ; PWC entry's TDR
(define-symbolic pwc-entry-partition-cp28  integer?)  ; PWC entry's partition (L1/L2 VM id)
(define-symbolic entity-tdr-cp28           integer?)  ; requesting entity's TDR
(define-symbolic entity-partition-cp28     integer?)  ; requesting entity's partition
(define-symbolic pwc-visible-cp28          boolean?)  ; PWC entry visible/usable by entity

(define cP28
  (assert
    (not (and pwc-visible-cp28
              (or (not (= entity-tdr-cp28 pwc-entry-tdr-cp28))
                  (not (= entity-partition-cp28 pwc-entry-partition-cp28)))))))
              ; PWC visible to non-owning TD/partition — IMPOSSIBLE

(define result-cP28 (verify cP28))
(displayln (if (unsat? result-cP28)
               "cP28 VERIFIED: PAGING_CACHE_CROSS_TD_CONFIDENTIALITY - Paging-structure cache entries confined to owning TD/partition"
               "cP28 VIOLATED: PAGING_CACHE_CROSS_TD_CONFIDENTIALITY - Paging-structure cache entry visible outside owning TD/partition"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP29: L2_PROFILING_ISOLATION  [tpP18]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic pmt-prof-cp29           integer?)  ; ATTRIBUTES.PMT_PROF value
(define-symbolic l2-perf-observation-cp29 boolean?) ; L2 perf/debug observation enabled
(define-symbolic observed-scope-cp29     integer?)  ; scope id of observed events
(define-symbolic current-td-scope-cp29   integer?)  ; current TD scope id

(define cP29
  (assert
    (not (or
      ;; profiling disabled + observation enabled — IMPOSSIBLE
      (and (= pmt-prof-cp29 PMT_PROF_DISABLED)
           l2-perf-observation-cp29)
      ;; profiling enabled + observed events outside current TD scope — IMPOSSIBLE
      (and (= pmt-prof-cp29 PMT_PROF_ENABLED)
           (not (= observed-scope-cp29 current-td-scope-cp29)))))))

(define result-cP29 (verify cP29))
(displayln (if (unsat? result-cP29)
               "cP29 VERIFIED: L2_PROFILING_ISOLATION - L2 profiling disabled by default and scoped to owning TD when enabled"
               "cP29 VIOLATED: L2_PROFILING_ISOLATION - L2 profiling observed activity outside owning TD scope"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP30: SPECULATIVE_L2_WALK_CHECK_BEFORE_FORWARD  [tpP20]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic speculative-l2-walk-cp30  boolean?)  ; speculative L2 walk occurred
(define-symbolic checks-passed-cp30        boolean?)  ; TD/HKID/PAMT/SEPT checks passed
(define-symbolic data-forwarded-cp30       boolean?)  ; data/metadata forwarded to dependents

(define cP30
  (assert
    (not (and speculative-l2-walk-cp30
              data-forwarded-cp30
              (not checks-passed-cp30)))))
              ; speculative forward before checks pass — IMPOSSIBLE

(define result-cP30 (verify cP30))
(displayln (if (unsat? result-cP30)
               "cP30 VERIFIED: SPECULATIVE_L2_WALK_CHECK_BEFORE_FORWARD - Speculative L2 walks gate forwarding on permission checks"
               "cP30 VIOLATED: SPECULATIVE_L2_WALK_CHECK_BEFORE_FORWARD - Speculative L2 walk forwarded data before checks passed"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP31: L1_PRIVATE_STATE_NOT_LIVE_ACROSS_L2_ENTRY  [tpP24]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic l2-entry-occurred-cp31     boolean?)  ; L2 VM entry occurred
(define-symbolic l1-private-value-cp31      integer?)  ; L1-private state value (pre-entry)
(define-symbolic l2-visible-value-cp31      integer?)  ; value visible to L2 post-entry
(define-symbolic explicitly-virtualized-cp31 boolean?) ; this value is part of virtualized subset

(define cP31
  (assert
    (not (and l2-entry-occurred-cp31
              (not explicitly-virtualized-cp31)
              (= l2-visible-value-cp31 l1-private-value-cp31)
              (not (= l1-private-value-cp31 0))))))
              ; non-virtualized L1-private value visible to L2 — IMPOSSIBLE

(define result-cP31 (verify cP31))
(displayln (if (unsat? result-cP31)
               "cP31 VERIFIED: L1_PRIVATE_STATE_NOT_LIVE_ACROSS_L2_ENTRY - Non-virtualized L1 state never visible to L2 after entry"
               "cP31 VIOLATED: L1_PRIVATE_STATE_NOT_LIVE_ACROSS_L2_ENTRY - L1-private residue visible to L2 after entry"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP32: HOST_DMA_BLOCKED_ON_L2_PRIVATE_ALIAS  [tpP25]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic l2-private-alias-backing-cp32 boolean?)  ; HPA backs an L2 private alias
(define-symbolic dma-hkid-cp32              integer?)      ; HKID used by the DMA transaction
(define-symbolic dma-hkid-is-shared-cp32    boolean?)      ; dma-hkid is shared/non-TDX HKID
(define-symbolic dma-access-result-cp32     integer?)      ; 0=denied/fault, 1=succeeded

(define cP32
  (assert
    (not (and l2-private-alias-backing-cp32
              dma-hkid-is-shared-cp32
              (= dma-access-result-cp32 DMA_SUCCEEDED)))))
              ; L2 private alias backing + shared-HKID DMA succeeded — IMPOSSIBLE

(define result-cP32 (verify cP32))
(displayln (if (unsat? result-cP32)
               "cP32 VERIFIED: HOST_DMA_BLOCKED_ON_L2_PRIVATE_ALIAS - Shared/non-TDX HKID DMA to L2 private alias backing pages is denied"
               "cP32 VIOLATED: HOST_DMA_BLOCKED_ON_L2_PRIVATE_ALIAS - Shared-HKID DMA succeeded against L2 private alias backing page"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ============================================================
;; ATTESTATION CONFIDENTIALITY PROPERTIES  [NEW — RAG]
;;
;;   No Speculative Exposure of Measurement State -> cP33
;;   Constant-Pattern Measurement Access Timing   -> cP34
;; ============================================================
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP33: NO_SPECULATIVE_EXPOSURE_OF_MEASUREMENT_STATE
;;
;; Property: MRTD, RTMR, TDINFO, report MAC inputs, aur
;;           intermediate hash/MAC state, non-authorized
;;           execution contexts ko speculative loads,
;;           transient execution, shared buffers, ya
;;           uncommitted faulting paths ke through visible
;;           ho — IMPOSSIBLE
;; Ref: Base Spec — measurement confidentiality and SEAM
;;      execution; ABI Spec — TDCS/RTMR opaque access
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic meas-state-value-cp33      integer?)  ; MRTD/RTMR/MAC intermediate value
(define-symbolic authorized-ctx-cp33        boolean?)  ; requester is authorized context
(define-symbolic speculative-path-cp33      boolean?)  ; access is through speculative path
(define-symbolic transient-visible-cp33     boolean?)  ; value became visible transiently
 
(define cP33
  (assert
    (not (and (not authorized-ctx-cp33)       ; non-authorized context
              (or speculative-path-cp33        ; speculative load path
                  transient-visible-cp33)      ; OR transient execution visibility
              (not (= meas-state-value-cp33 0))))))
              ; non-zero meas state visible to unauthorized context — IMPOSSIBLE
 
(define result-cP33 (verify cP33))
(displayln (if (unsat? result-cP33)
               "cP33 VERIFIED: NO_SPECULATIVE_EXPOSURE_OF_MEASUREMENT_STATE - MRTD/RTMR/MAC state not visible to unauthorized contexts via speculation"
               "cP33 VIOLATED: NO_SPECULATIVE_EXPOSURE_OF_MEASUREMENT_STATE - Measurement state leaked to unauthorized context via speculative path"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP34: CONSTANT_PATTERN_MEASUREMENT_ACCESS_TIMING
;;
;; Property: MRTD/RTMR/report-MAC datapath ka access
;;           latency, retry behavior, ya observable
;;           contention secret measurement register
;;           contents ya intermediate hash values par
;;           depend kare — IMPOSSIBLE
;; Ref: Intel TDX Base Spec — SEAM measurement handling;
;;      Intel SDM — side-channel and speculative execution
;;      mitigation topics
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic meas-secret-content-cp34  integer?)  ; secret value in MRTD/RTMR/hash
(define-symbolic observed-latency-cp34     integer?)  ; observable access latency / contention
(define-symbolic baseline-latency-cp34     integer?)  ; expected constant-time baseline latency
 
(define cP34
  (assert
    (not (and (not (= meas-secret-content-cp34 0))   ; non-trivial secret content
              (not (= observed-latency-cp34
                      baseline-latency-cp34))))))      ; latency differs from baseline — IMPOSSIBLE
              ; secret-dependent timing variation — IMPOSSIBLE
 
(define result-cP34 (verify cP34))
(displayln (if (unsat? result-cP34)
               "cP34 VERIFIED: CONSTANT_PATTERN_MEASUREMENT_ACCESS_TIMING - MRTD/RTMR/MAC access latency is secret-independent"
               "cP34 VIOLATED: CONSTANT_PATTERN_MEASUREMENT_ACCESS_TIMING - Secret-dependent timing variation detected in measurement datapath"))
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Final Summary
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(displayln "\n=== CONFIDENTIALITY VERIFICATION SUMMARY ===")

(define all-results
  (list (cons "cP1"  result-cP1)
        (cons "cP2"  result-cP2)
        (cons "cP3"  result-cP3)
        (cons "cP4"  result-cP4)
        (cons "cP5"  result-cP5)
        (cons "cP6"  result-cP6)
        (cons "cP7"  result-cP7)
        (cons "cP8"  result-cP8)
        (cons "cP9"  result-cP9)
        (cons "cP10" result-cP10)
        (cons "cP11" result-cP11)
        (cons "cP40" result-cP40)
        (cons "cP41" result-cP41)
        (cons "cP42" result-cP42)
        (cons "cP43" result-cP43)
        (cons "cP44" result-cP44)
        (cons "cP45" result-cP45)
        ;; --- MKTME CONFIDENTIALITY PROPERTIES ---
        (cons "cP12"  result-cM1)
        (cons "cP13"  result-cM2)
        (cons "cP14"  result-cM3)
        (cons "cP15"  result-cM4)
        ;; --- ATTESTATION CONFIDENTIALITY PROPERTIES ---
        (cons "cP16"  result-cA1)
        (cons "cP17"  result-cA2)
        (cons "cP18"  result-cA3)
        (cons "cP19"  result-cA4)
        (cons "cP20"  result-cA5)
        ;; --- L1/L2 PARTITIONING CONFIDENTIALITY [NEW] ---
        (cons "cP21 [DocP1-AliasColl]"   result-cP21)
        (cons "cP22 [DocP5-HKIDBind]"    result-cP22)
        (cons "cP23 [DocP6-TLBFlush]"    result-cP23)
        ;; --- ADDITIONAL L1/L2 PARTITIONING CONFIDENTIALITY [NEW] ---
        (cons "cP24 [tpP3-L2BlockedNoAccess]" result-cP24)
        (cons "cP25 [tpP5-TLBTagging]"        result-cP25)
        (cons "cP26 [tpP9-HostExitSanitized]" result-cP26)
        (cons "cP27 [tpP11-SharedBitConsist]" result-cP27)
        (cons "cP28 [tpP15-PWCCrossTD]"       result-cP28)
        (cons "cP29 [tpP18-ProfIsolation]"    result-cP29)
        (cons "cP30 [tpP20-SpecWalkCheck]"    result-cP30)
        (cons "cP31 [tpP24-L1StateNotLive]"   result-cP31)
        (cons "cP32 [tpP25-HostDMABlocked]"   result-cP32)
        ;; --- ATTESTATION CONFIDENTIALITY PROPERTIES [RAG NEW] ---
        (cons "cP33 [NoSpecMeasExposure]"      result-cP33)
        (cons "cP34 [ConstTimingMeasAccess]"   result-cP34)))
 

(for ([r all-results])
  (printf "~a: ~a\n"
          (car r)
          (if (unsat? (cdr r)) "VERIFIED ✓" "VIOLATED ✗")))

(provide (all-defined-out))
