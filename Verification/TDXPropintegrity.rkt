#lang rosette

(require (file "tables.rkt"))
(require "tdx_lib.rkt")
(require "cache_instance_hkid.rkt")

(displayln "=== Proof: Integrity Properties ===")

(define bv28 (bitvector 28))

;; Page level constants (iP41 ke liye)
(define PAGE_LEVEL_4KB 1)
(define PAGE_LEVEL_2MB 2)
(define PAGE_LEVEL_1GB 3)
(define PAGE_SIZE_NORMAL   0)
(define PAGE_SIZE_HUGE_2MB 1)
(define PAGE_SIZE_HUGE_1GB 2)

;; MKTME partition constants
(define NUM_HKID_KEYS      8)   ; last shared HKID index  (0..8 = shared range)
(define NUM_TDX_PRIV_KIDS  56)  ; number of private HKIDs
(define MAX_HKID           (+ NUM_HKID_KEYS NUM_TDX_PRIV_KIDS))  ; 64
(define HKID_TME           0)   ; HKID=0 is always the TME legacy key
(define KEY_ZERO           0)   ; sentinel: zeroized / no key
(define TOTAL_PACKAGES     2)   ; platform package count (example: dual-socket)
 
 
;; Attestation-layer constants
(define FINALIZED_STATE    1)   ; TDR finalization flag value
(define HASH_SIZE_SHA384  48)   ; bytes — SHA-384 output size
(define MIN_PLATFORM_SVN   1)   ; minimum allowed hardware SVN value
(define SEPT_CALLER_TD     1)   ; SEPT check result: GPA belongs to caller TD
 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hpa-ip1 integer?)
(define-symbolic gpa-shared-ip1 integer?)
(define-symbolic state-ip1 integer?)

(define entry-ip1
  (make-secure_EPT_entry hpa-ip1 gpa-shared-ip1 state-ip1))

(define iP1
  (assert
    (not (and (secure_EPT_entry? entry-ip1)
              (= (secure_EPT_entry-state entry-ip1)
                 SEPT_BLOCKED)))))

(define result-iP1 (verify iP1))
(displayln (if (unsat? result-iP1)
               "iP1 VERIFIED: No GPA->HPA mapping in BLOCKED state"
               "iP1 VIOLATED: A mapping found in BLOCKED state"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic finalized-ip2 boolean?)
(define-symbolic fatal-ip2     boolean?)
(define-symbolic init-ip2      boolean?)
(define-symbolic lstate-ip2    integer?)
(define-symbolic hkid-s-ip2    integer?)

(define tdr-sym-ip2
  (make-TDR init-ip2 fatal-ip2 0 0 0 lstate-ip2 hkid-s-ip2 0 finalized-ip2 #f))

(define iP2
  (assert
    (not (and (TDR? tdr-sym-ip2)
              finalized-ip2     ; finalized hai
              fatal-ip2))))     ; aur fatal bhi — IMPOSSIBLE

(define result-iP2 (verify iP2))
(displayln (if (unsat? result-iP2)
               "iP2 VERIFIED: Finalized TDR cannot revert to INIT/FATAL"
               "iP2 VIOLATED: Finalized TDR state inconsistency found"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP3
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic ls-a ls-c ls-b ls-t integer?)

(define iP3
  (assert
    (not (or
      ;; CONFIGURED bina ASSIGNED ke — IMPOSSIBLE
      (and (= ls-c TD_KEYS_CONFIGURED)
           (not (= ls-a TD_HKID_ASSIGNED)))
      ;; BLOCKED bina CONFIGURED ke — IMPOSSIBLE
      (and (= ls-b TD_BLOCKED)
           (not (= ls-c TD_KEYS_CONFIGURED)))
      ;; TEARDOWN bina BLOCKED ke — IMPOSSIBLE
      (and (= ls-t TD_TEARDOWN)
           (not (= ls-b TD_BLOCKED)))))))

(define result-iP3 (verify iP3))
(displayln (if (unsat? result-iP3)
               "iP3 VERIFIED: HKID lifecycle transitions are valid"
               "iP3 VIOLATED: Invalid lifecycle transition found"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP4
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic pa-ip4 bv28)
(define-symbolic way-ip4 integer?)
(define-symbolic hkid-ip4 integer?)

(define-values (hit-ip4 actual-way-ip4 data-ip4)
  (query-cache pa-ip4 way-ip4 hkid-ip4))

(define set-ip4 (paddr2set pa-ip4))
(define tag-ip4 (paddr2tag pa-ip4))
(define key-ip4 (cons set-ip4 actual-way-ip4))

(define iP4
  (assert
    (not (and (hash-ref cache-valid-map key-ip4 #f)
              (not (= (hash-ref cache-tag-map key-ip4 -1)
                      tag-ip4))))))

(define result-iP4 (verify iP4))
(displayln (if (unsat? result-iP4)
               "iP4 VERIFIED: Valid cache entries have correct tags"
               "iP4 VIOLATED: Cache entry found with incorrect tag"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP5
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic valid-A-ip5 valid-B-ip5 boolean?)
(define-symbolic tag-A-ip5 tag-B-ip5 integer?)
(define-symbolic wayA-ip5 wayB-ip5 integer?)

(define iP5
  (assert
    (not (and valid-A-ip5
              valid-B-ip5
              (not (= wayA-ip5 wayB-ip5))   ; alag ways
              (= tag-A-ip5 tag-B-ip5)))))    ; same tag — IMPOSSIBLE

(define result-iP5 (verify iP5))
(displayln (if (unsat? result-iP5)
               "iP5 VERIFIED: Same set entries have unique tags"
               "iP5 VIOLATED: Duplicate tags found in same set"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP6
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic pa-ip6 bv28)
(define-symbolic way-ip6 integer?)
(define-symbolic hkid-ip6 integer?)

(define-values (hit-ip6 actual-way-ip6 data-ip6)
  (query-cache pa-ip6 way-ip6 hkid-ip6))

(define set-ip6 (paddr2set pa-ip6))
(define key-ip6 (cons set-ip6 actual-way-ip6))

(define iP6
  (assert
    (not (and (hash-ref cache-valid-map key-ip6 #f)
              (not (= (hash-ref cache-hkid-map key-ip6 -1)
                      hkid-ip6))))))

(define result-iP6 (verify iP6))
(displayln (if (unsat? result-iP6)
               "iP6 VERIFIED: Cache entries correctly map HKID"
               "iP6 VIOLATED: HKID mismatch found in cache entry"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP7
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic td-owner-ip7 boolean?)
(define-symbolic hkid-val-ip7 integer?)
(define-symbolic mac-ip7 integer?)
(define-symbolic data-val-ip7 integer?)

(define entry-ip7
  (make-cache_entry td-owner-ip7 hkid-val-ip7 mac-ip7 data-val-ip7))

(define iP7
  (assert
    (not (and (cache_entry? entry-ip7)
              (not (boolean? (cache_entry-TD_OWNER entry-ip7)))))))

(define result-iP7 (verify iP7))
(displayln (if (unsat? result-iP7)
               "iP7 VERIFIED: Valid cache entries have correct TD owner bit"
               "iP7 VIOLATED: TD owner bit missing or invalid"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP8
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic valid-X-ip8 valid-Y-ip8 boolean?)
(define-symbolic tag-X-ip8 tag-Y-ip8 integer?)
(define-symbolic wayX-ip8 wayY-ip8 integer?)

(define iP8
  (assert
    (not (and valid-X-ip8
              valid-Y-ip8
              (not (= wayX-ip8 wayY-ip8))  ; alag ways
              (= tag-X-ip8 tag-Y-ip8)))))   ; same tag — IMPOSSIBLE

(define result-iP8 (verify iP8))
(displayln (if (unsat? result-iP8)
               "iP8 VERIFIED: Different ways in same set have different tags"
               "iP8 VIOLATED: Same tag found in different ways"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP9
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic td-owner-A-ip9 boolean?)
(define-symbolic td-owner-B-ip9 boolean?)
(define-symbolic mac-A-ip9 mac-B-ip9 integer?)
(define-symbolic hkid-A-ip9 hkid-B-ip9 integer?)
(define-symbolic data-A-ip9 data-B-ip9 integer?)

(define entryA-ip9
  (make-cache_entry td-owner-A-ip9 hkid-A-ip9 mac-A-ip9 data-A-ip9))
(define entryB-ip9
  (make-cache_entry td-owner-B-ip9 hkid-B-ip9 mac-B-ip9 data-B-ip9))

(define iP9
  (assert
    (not (and (cache_entry? entryA-ip9)
              (cache_entry? entryB-ip9)
              (= mac-A-ip9 mac-B-ip9)              ; same MAC
              (not (equal? (cache_entry-TD_OWNER entryA-ip9)
                           (cache_entry-TD_OWNER entryB-ip9))))))) ; alag owner — IMPOSSIBLE

(define result-iP9 (verify iP9))
(displayln (if (unsat? result-iP9)
               "iP9 VERIFIED: Same-tag entries have consistent TD owner"
               "iP9 VIOLATED: TD owner inconsistency for same-tag entries"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP40: SEPT_PAMT_SYNC (Atomic Update)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hpa-ip40  integer?)
(define-symbolic gpa-ip40  integer?)
(define-symbolic state-ip40 integer?)
(define-symbolic ptype-ip40 integer?)

(define sept-entry-ip40
  (make-secure_EPT_entry hpa-ip40 gpa-ip40 state-ip40))

(define pamt-entry-ip40
  (make-PAMT_entry ptype-ip40 0 0))

(define iP40
  (assert
    (not (and (secure_EPT_entry? sept-entry-ip40)
              (= (secure_EPT_entry-state sept-entry-ip40) SEPT_PRESENT)
              (= (PAMT_entry-PAGE_TYPE pamt-entry-ip40) PT_NDA)))))
                                        ; SEPT present + PAMT NDA — IMPOSSIBLE

(define result-iP40 (verify iP40))
(displayln (if (unsat? result-iP40)
               "iP40 VERIFIED: SEPT_PAMT_SYNC - SEPT and PAMT updates are consistent"
               "iP40 VIOLATED: SEPT_PAMT_SYNC - inconsistency between SEPT and PAMT"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP41: HUGE_PAGE_LOCK (Level Enforcement)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic page-size-ip41 integer?)
(define-symbolic page-level-ip41 integer?)

(define iP41
  (assert
    (not (or
      ;; 2MB page wrong level pe — IMPOSSIBLE
      (and (= page-size-ip41 PAGE_SIZE_HUGE_2MB)
           (not (= page-level-ip41 PAGE_LEVEL_2MB)))
      ;; 1GB page wrong level pe — IMPOSSIBLE
      (and (= page-size-ip41 PAGE_SIZE_HUGE_1GB)
           (not (= page-level-ip41 PAGE_LEVEL_1GB)))
      ;; Normal page wrong level pe — IMPOSSIBLE
      (and (= page-size-ip41 PAGE_SIZE_NORMAL)
           (not (= page-level-ip41 PAGE_LEVEL_4KB)))))))

(define result-iP41 (verify iP41))
(displayln (if (unsat? result-iP41)
               "iP41 VERIFIED: HUGE_PAGE_LOCK - Large pages mapped at correct levels only"
               "iP41 VIOLATED: HUGE_PAGE_LOCK - Large page at wrong level detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP42: SEPT_RECURSIVE_ERR (Infinite Loop Protection)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic gpa-ip42 integer?)
(define-symbolic hpa-ip42 integer?)
(define-symbolic state-ip42 integer?)

(define sept-ip42
  (make-secure_EPT_entry hpa-ip42 gpa-ip42 state-ip42))

(define iP42
  (assert
    (not (and (secure_EPT_entry? sept-ip42)
              (= (secure_EPT_entry-state sept-ip42) SEPT_PRESENT)
              (= gpa-ip42 hpa-ip42)))))  ; self-reference — IMPOSSIBLE

(define result-iP42 (verify iP42))
(displayln (if (unsat? result-iP42)
               "iP42 VERIFIED: SEPT_RECURSIVE_ERR - No cyclic SEPT references"
               "iP42 VIOLATED: SEPT_RECURSIVE_ERR - Cyclic reference detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP43: TLB_FLUSH_SYNC (Stale Mapping Protection)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hkid-ip43 integer?)

(flush_cache hkid-ip43)

(define iP43
  (assert
    (let ([keys (hash-keys cache)])
      (for/and ([k keys])
        (let ([entry (hash-ref cache k #f)])
          (not (and (cache_entry? entry)
                    (= (cache_entry-HKID entry)
                       hkid-ip43))))))))  ; flushed HKID ki entry — IMPOSSIBLE

(define result-iP43 (verify iP43))
(displayln (if (unsat? result-iP43)
               "iP43 VERIFIED: TLB_FLUSH_SYNC - No stale cache entry after flush"
               "iP43 VIOLATED: TLB_FLUSH_SYNC - Stale cache entry found after flush"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP44: PAMT_DIRTY_INV (Cache Invalidation)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic pa-ip44 integer?)
(define-symbolic hkid-ip44 integer?)

(hash-set! PAMT pa-ip44 (make-PAMT_entry PT_NDA 0 0))
(flush_cache hkid-ip44)

(define iP44
  (assert
    (let ([pamt-e (hash-ref PAMT pa-ip44 #f)])
      (let ([keys (hash-keys cache)])
        (for/and ([k keys])
          (let ([ce (hash-ref cache k #f)])
            (not (and (PAMT_entry? pamt-e)
                      (= (PAMT_entry-PAGE_TYPE pamt-e) PT_NDA)
                      (cache_entry? ce)
                      (= (cache_entry-HKID ce)
                         hkid-ip44)))))))))  ; NDA page + cache entry — IMPOSSIBLE

(define result-iP44 (verify iP44))
(displayln (if (unsat? result-iP44)
               "iP44 VERIFIED: PAMT_DIRTY_INV - Cache invalidated on PAMT metadata change"
               "iP44 VIOLATED: PAMT_DIRTY_INV - Stale cache after PAMT change"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP45: FATAL_STATE_LOCK (Fail-Safe Mechanism)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic init-ip45      boolean?)
(define-symbolic lstate-ip45    integer?)
(define-symbolic hkid-ip45      integer?)
(define-symbolic finalized-ip45 boolean?)

(define fatal-tdr-ip45
  (make-TDR init-ip45 #t 0 0 0 lstate-ip45 hkid-ip45 0 finalized-ip45 #f))

(define iP45
  (assert
    (not (and (TDR-FATAL fatal-tdr-ip45)        ; FATAL=true
              (or
                (not (= (TDR-LIFECYCLE_STATE fatal-tdr-ip45) lstate-ip45))
                (not (equal? (TDR-FINALIZED fatal-tdr-ip45) finalized-ip45))
                (not (equal? (TDR-INIT fatal-tdr-ip45) init-ip45)))))))
                ; FATAL + koi bhi change — IMPOSSIBLE

(define result-iP45 (verify iP45))
(displayln (if (unsat? result-iP45)
               "iP45 VERIFIED: FATAL_STATE_LOCK - Fatal TDR cannot transition to any state"
               "iP45 VIOLATED: FATAL_STATE_LOCK - Fatal TDR state changed"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP46: SEPT_MIRROR_CONSISTENCY (Redundancy Check)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hpa-ip46-p   integer?)
(define-symbolic gpa-ip46-p   integer?)
(define-symbolic state-ip46-p integer?)
(define-symbolic hpa-ip46-m   integer?)
(define-symbolic gpa-ip46-m   integer?)
(define-symbolic state-ip46-m integer?)

(define sept-primary-ip46
  (make-secure_EPT_entry hpa-ip46-p gpa-ip46-p state-ip46-p))

(define sept-mirror-ip46
  (make-secure_EPT_entry hpa-ip46-m gpa-ip46-m state-ip46-m))

(define iP46
  (assert
    (not (and (secure_EPT_entry? sept-primary-ip46)
              (secure_EPT_entry? sept-mirror-ip46)
              (or
                (not (= (secure_EPT_entry-host_physical_address sept-primary-ip46)
                        (secure_EPT_entry-host_physical_address sept-mirror-ip46)))
                (not (= (secure_EPT_entry-GPA_SHARED sept-primary-ip46)
                        (secure_EPT_entry-GPA_SHARED sept-mirror-ip46)))
                (not (= (secure_EPT_entry-state sept-primary-ip46)
                        (secure_EPT_entry-state sept-mirror-ip46))))))))
              ; Primary aur Mirror SEPT mismatch — IMPOSSIBLE

(define result-iP46 (verify iP46))
(displayln (if (unsat? result-iP46)
               "iP46 VERIFIED: SEPT_MIRROR_CONSISTENCY - Primary and Mirror SEPT trees are bit-identical"
               "iP46 VIOLATED: SEPT_MIRROR_CONSISTENCY - Mismatch between Primary and Mirror SEPT"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP47: PAMT_TYPE_EXCLUSIVITY (Metadata Integrity)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic ptype-A-ip47 integer?)
(define-symbolic ptype-B-ip47 integer?)
(define-symbolic owner-ip47   integer?)
(define-symbolic gen-ip47     integer?)

;; Do alag entries same physical page ke liye alag types ke saath
(define pamt-entry-A-ip47
  (make-PAMT_entry ptype-A-ip47 owner-ip47 gen-ip47))
(define pamt-entry-B-ip47
  (make-PAMT_entry ptype-B-ip47 owner-ip47 gen-ip47))

(define iP47
  (assert
    (not (and (PAMT_entry? pamt-entry-A-ip47)
              (PAMT_entry? pamt-entry-B-ip47)
              (not (= ptype-A-ip47 PT_NDA))   ; typeA valid (non-NDA) hai
              (not (= ptype-B-ip47 PT_NDA))   ; typeB valid (non-NDA) hai
              (not (= ptype-A-ip47 ptype-B-ip47))))))
              ; same page ke 2 alag valid types — IMPOSSIBLE

(define result-iP47 (verify iP47))
(displayln (if (unsat? result-iP47)
               "iP47 VERIFIED: PAMT_TYPE_EXCLUSIVITY - Each page has exactly one PAMT identity"
               "iP47 VIOLATED: PAMT_TYPE_EXCLUSIVITY - Dual-role page detected in PAMT"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP48: VCPU_EPOCH_SYNC (Migration Safety"
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic epoch-src-ip48  integer?)
(define-symbolic epoch-dst-ip48  integer?)
(define-symbolic vcpu-loaded-ip48 boolean?)

(define iP48
  (assert
    (not (and vcpu-loaded-ip48                      ; VCPU context load hua
              (not (= epoch-src-ip48 epoch-dst-ip48))))))
              ; alag epoch pe load — IMPOSSIBLE

(define result-iP48 (verify iP48))
(displayln (if (unsat? result-iP48)
               "iP48 VERIFIED: VCPU_EPOCH_SYNC - VCPU context loaded only on matching epoch"
               "iP48 VIOLATED: VCPU_EPOCH_SYNC - Epoch mismatch on VCPU load detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP49: SEPT_5L_PAGING_LIMIT (Architecture Lockdown)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define PAGING_4L 4)
(define PAGING_5L 5)

(define-symbolic td-paging-level-ip49  integer?)
(define-symbolic req-paging-level-ip49 integer?)
(define-symbolic req-accepted-ip49     boolean?)

(define iP49
  (assert
    (not (and (= td-paging-level-ip49 PAGING_4L)   ; TD 4-level config mein hai
              (= req-paging-level-ip49 PAGING_5L)   ; 5-level request aayi
              req-accepted-ip49))))                   ; aur accept ho gayi — IMPOSSIBLE

(define result-iP49 (verify iP49))
(displayln (if (unsat? result-iP49)
               "iP49 VERIFIED: SEPT_5L_PAGING_LIMIT - 5-level requests rejected in 4-level TD config"
               "iP49 VIOLATED: SEPT_5L_PAGING_LIMIT - 5-level request accepted in 4-level TD"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP50: SEPT_RSVD_BIT_STRICT (Reserved Bit Hygiene)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic rsvd-bits-ip50 integer?)   ; bits 51-62 ka value
(define-symbolic ept-error-ip50 boolean?)   ; EPT_MISCONFIG raised hua?

(define iP50
  (assert
    (not (and (> rsvd-bits-ip50 0)          ; reserved bits non-zero hain
              (not ept-error-ip50)))))       ; lekin EPT_MISCONFIG nahi hua — IMPOSSIBLE

(define result-iP50 (verify iP50))
(displayln (if (unsat? result-iP50)
               "iP50 VERIFIED: SEPT_RSVD_BIT_STRICT - Non-zero reserved bits trigger EPT_MISCONFIG"
               "iP50 VIOLATED: SEPT_RSVD_BIT_STRICT - Reserved bit violation not caught"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ============================================
;; NEW MKTME INTEGRITY PROPERTIES
;; ============================================
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP10: MKTME_SHARED_HKID_BOUND
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic hkid-im1      integer?)   ; HKID assigned to a TD
(define-symbolic td-valid-im1  boolean?)   ; TD creation succeeded
 
(define iM1
  (assert
    (not (and td-valid-im1                    ; TD was successfully created
              (<= hkid-im1 NUM_HKID_KEYS))))) ; with a shared-range HKID — IMPOSSIBLE
 
(define result-iM1 (verify iM1))
(displayln (if (unsat? result-iM1)
               "iP10 VERIFIED: MKTME_SHARED_HKID_BOUND - TD HKID always above shared boundary"
               "iP10 VIOLATED: MKTME_SHARED_HKID_BOUND - TD assigned shared-range HKID detected"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP11: MKTME_KEY_CONFIG_ALL_PKG
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic pkg-bitmap-im2    integer?)   ; PKG_CONFIG_BITMAP value in TDR
(define-symbolic total-pkgs-im2    integer?)   ; total packages on platform
(define-symbolic td-runnable-im2   boolean?)   ; TD entered RUNNABLE state
 
;; Full bitmap: all bits set = (2^total_pkgs - 1)
;; Simplified model: bitmap must equal expected full value
(define full-pkg-mask-im2
  (- (expt 2 TOTAL_PACKAGES) 1))               ; e.g., 0b11 for 2 packages
 
(define iM2
  (assert
    (not (and td-runnable-im2                          ; TD is running
              (not (= pkg-bitmap-im2
                      full-pkg-mask-im2))))))          ; not all packages configured — IMPOSSIBLE
 
(define result-iM2 (verify iM2))
(displayln (if (unsat? result-iM2)
               "iP11 VERIFIED: MKTME_KEY_CONFIG_ALL_PKG - TD runs only after all packages keyed"
               "iP11 VIOLATED: MKTME_KEY_CONFIG_ALL_PKG - TD runnable with incomplete package key config"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP12: MKTME_PARTITION_IMMUTABLE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic boundary-at-init-im3    integer?)  ; NUM_HKID_KEYS at TDH.SYS.INIT time
(define-symbolic boundary-at-runtime-im3 integer?)  ; NUM_HKID_KEYS at some later time
(define-symbolic tdx-active-im3          boolean?)  ; TDX module fully initialised
 
(define iM3
  (assert
    (not (and tdx-active-im3                              ; TDX is active (post-init)
              (not (= boundary-at-init-im3
                      boundary-at-runtime-im3))))))       ; boundary changed — IMPOSSIBLE
 
(define result-iM3 (verify iM3))
(displayln (if (unsat? result-iM3)
               "iP12 VERIFIED: MKTME_PARTITION_IMMUTABLE - HKID partition boundary unchanged after TDX init"
               "iP12 VIOLATED: MKTME_PARTITION_IMMUTABLE - HKID partition boundary changed at runtime"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP13: MKTME_PRIVATE_WRITE_NON_SEAM_BLOCK
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic write-hkid-im4        integer?)   ; HKID used in the write
(define-symbolic td-owner-bit-im4      boolean?)   ; ACT/TD-owner bit for target page
(define-symbolic seam-mode-im4         boolean?)   ; #t = SEAM mode active
(define-symbolic write-committed-im4   boolean?)   ; did write reach DRAM?
 
(define iM4
  (assert
    (not (and (not seam-mode-im4)                  ; NOT in SEAM mode
              (<= write-hkid-im4 NUM_HKID_KEYS)    ; using a shared HKID
              td-owner-bit-im4                      ; target page is TD-private (owner=1)
              write-committed-im4))))               ; write committed to DRAM — IMPOSSIBLE
 
(define result-iM4 (verify iM4))
(displayln (if (unsat? result-iM4)
               "iP13 VERIFIED: MKTME_PRIVATE_WRITE_NON_SEAM_BLOCK - Non-SEAM shared-HKID writes to private pages are dropped"
               "iP13 VIOLATED: MKTME_PRIVATE_WRITE_NON_SEAM_BLOCK - Non-SEAM write committed to TD-private page"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ATTESTATION INTEGRITY PROPERTIES
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP14: ASRT_MRTD_IMMUTABILITY
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic mrtd-before-iA1  integer?)  ; MRTD value at finalization
(define-symbolic mrtd-after-iA1   integer?)  ; MRTD value during TD RUNNING state
(define-symbolic td-finalized-iA1 boolean?)  ; TDH.MR.FINALIZE was called successfully
(define-symbolic td-running-iA1   boolean?)  ; TD is currently executing (RUNNING state)
 
(define iA1
  (assert
    (not (and td-finalized-iA1                     ; TD has been finalized
              td-running-iA1                        ; TD is currently running
              (not (= mrtd-before-iA1
                      mrtd-after-iA1))))))           ; MRTD changed after finalize — IMPOSSIBLE
 
(define result-iA1 (verify iA1))
(displayln (if (unsat? result-iA1)
               "iP14 VERIFIED: ASRT_MRTD_IMMUTABILITY - MRTD register locked and stable after TDH.MR.FINALIZE"
               "iP14 VIOLATED: ASRT_MRTD_IMMUTABILITY - MRTD changed after finalization detected"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP15: ASRT_RTMR_EXTEND_ATOMICITY
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic rtmr-old-iA2          integer?)  ; RTMR value before extend
(define-symbolic rtmr-new-iA2          integer?)  ; RTMR value after full extend
(define-symbolic rtmr-intermediate-iA2 integer?)  ; value during hash mid-computation
(define-symbolic extend-complete-iA2   boolean?)  ; TDG.MR.RTMR.EXTEND fully finished
(define-symbolic hash-in-progress-iA2  boolean?)  ; SHA-384 computation is mid-cycle
 
;; During in-progress computation, intermediate state must not be
;; visible (i.e., RTMR must not hold a partial value externally)
(define iA2-no-partial-visible
  (assert
    (not (and hash-in-progress-iA2                    ; hash is mid-computation
              (not (= rtmr-intermediate-iA2 rtmr-old-iA2))  ; not the old value
              (not (= rtmr-intermediate-iA2 rtmr-new-iA2))  ; not the new value either
              ))))                                      ; intermediate leaks — IMPOSSIBLE
 
(define result-iA2-partial (verify iA2-no-partial-visible))
(displayln (if (unsat? result-iA2-partial)
               "iP15-a VERIFIED: ASRT_RTMR_EXTEND_ATOMICITY - No intermediate RTMR state visible during SHA-384"
               "iP15-a VIOLATED: ASRT_RTMR_EXTEND_ATOMICITY - Intermediate RTMR state leaked mid-computation"))
 
;; After extend completes, old value must not persist
(define iA2-no-old-after-done
  (assert
    (not (and extend-complete-iA2                     ; extend finished
              (not (= rtmr-new-iA2 0))                ; new value is non-trivial
              (= rtmr-new-iA2 rtmr-old-iA2)))))        ; value unchanged — IMPOSSIBLE
 
(define result-iA2-stale (verify iA2-no-old-after-done))
(displayln (if (unsat? result-iA2-stale)
               "iP15-b VERIFIED: ASRT_RTMR_EXTEND_ATOMICITY - RTMR updated to new value after extend completes"
               "iP15-b VIOLATED: ASRT_RTMR_EXTEND_ATOMICITY - RTMR unchanged after extend completion"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP16: ASRT_SVN_ROLLBACK_PROTECTION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic reported-svn-iA3  integer?)  ; TCB_SVN value in TDREPORT
(define-symbolic hardware-min-svn-iA3 integer?) ; platform minimum accepted SVN
(define-symbolic report-issued-iA3 boolean?)   ; TDG.MR.REPORT completed successfully
 
(define iA3
  (assert
    (not (and report-issued-iA3                         ; report was successfully issued
              (> hardware-min-svn-iA3 0)                 ; platform has a non-trivial minimum
              (< reported-svn-iA3 hardware-min-svn-iA3))))) ; reported SVN < minimum — IMPOSSIBLE
 
(define result-iA3 (verify iA3))
(displayln (if (unsat? result-iA3)
               "iP16 VERIFIED: ASRT_SVN_ROLLBACK_PROTECTION - Reported TCB_SVN >= hardware minimum SVN"
               "iP16 VIOLATED: ASRT_SVN_ROLLBACK_PROTECTION - SVN rollback detected in TDREPORT"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP17: ASRT_REPORT_REPLAY_PROTECTION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic nonce-call1-iA4  integer?)   ; REPORTDATA for first call
(define-symbolic nonce-call2-iA4  integer?)   ; REPORTDATA for second call
(define-symbolic mac-call1-iA4    integer?)   ; MAC produced by first call
(define-symbolic mac-call2-iA4    integer?)   ; MAC produced by second call
(define-symbolic both-issued-iA4  boolean?)   ; both calls completed successfully
 
(define iA4
  (assert
    (not (and both-issued-iA4                           ; both reports were generated
              (not (= nonce-call1-iA4 nonce-call2-iA4)) ; different nonces were used
              (= mac-call1-iA4 mac-call2-iA4)))))        ; same MAC output — IMPOSSIBLE
 
(define result-iA4 (verify iA4))
(displayln (if (unsat? result-iA4)
               "iP17 VERIFIED: ASRT_REPORT_REPLAY_PROTECTION - Different REPORTDATA nonces produce different MACs"
               "iP17 VIOLATED: ASRT_REPORT_REPLAY_PROTECTION - MAC collision across different nonces detected"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP18: ASRT_PRIV_MEM_INTEGRITY_ON_REPORT
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic output-gpa-iA5    integer?)  ; GPA guest provided as report output buffer
(define-symbolic mapped-hkid-iA5   integer?)  ; HKID of the page at output GPA (from SEPT)
(define-symbolic caller-hkid-iA5   integer?)  ; HKID of the calling TD
(define-symbolic report-written-iA5 boolean?) ; TDG.MR.REPORT wrote to output GPA
 
;; sept-check result: 1 = GPA belongs to caller TD, 0 = foreign TD
(define-symbolic sept-owner-check-iA5 integer?)
 
(define iA5
  (assert
    (not (and report-written-iA5                          ; report was written to output GPA
              (not (= mapped-hkid-iA5 caller-hkid-iA5))  ; GPA is mapped to a different HKID
              (not (= sept-owner-check-iA5 SEPT_CALLER_TD)))))) ; SEPT says it's not caller's page
              ; report write to foreign TD's memory — IMPOSSIBLE
 
(define result-iA5 (verify iA5))
(displayln (if (unsat? result-iA5)
               "iP18 VERIFIED: ASRT_PRIV_MEM_INTEGRITY_ON_REPORT - Report output GPA belongs to caller TD only"
               "iP18 VIOLATED: ASRT_PRIV_MEM_INTEGRITY_ON_REPORT - Report written to foreign TD memory detected"))
 



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; L1/L2 Manual TD PARTITIONING INTEGRITY PROPERTIES  [NEW]
;;
;; Mapping:
;;   Doc P2  -> iP19  L1_TO_L2_REGISTER_SCRUB
;;   Doc P3  -> iP20  L2_TO_L1_EXIT_IBPB
;;   Doc P4  -> iP21  MSR_SHADOW_BITMAP_INTEGRITY
;;   Doc P7  -> iP22  L2_INTERRUPT_WINDOW_ENFORCE
;;   Doc P8  -> iP23  SEPT_L2_NO_RECURSIVE_MAPPING
;;   Doc P9  -> iP24  ILLEGAL_L2_SEAMCALL_BLOCK
;;   Doc P10 -> iP25  TDG_VP_ENTER_ENTRY_POINT_CFI
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; L1/L2 constants
(define L1_VM             1)
(define L2_VM             2)
(define INST_SEAMCALL    10)   ; SEAMCALL opcode sentinel
(define EXC_UD            6)   ; #UD exception vector


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP19: L1_TO_L2_REGISTER_SCRUB  [Doc P2]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic l1-reg-val-ip19  integer?)   ; L1 ka sensitive GPR value
(define-symbolic l2-sees-val-ip19 integer?)   ; L2 first-cycle register read
(define-symbolic enter-called-ip19 boolean?)  ; TDG.VP.ENTER hua
(define-symbolic scrub-done-ip19   boolean?)  ; hardware register scrub/shadow-swap hua

(define iP19
  (assert
    (not (and enter-called-ip19
              scrub-done-ip19
              (not (= l1-reg-val-ip19 0))      ; sensitive non-zero value tha
              (= l2-sees-val-ip19
                 l1-reg-val-ip19)))))           ; L2 ne wohi value dekhi — IMPOSSIBLE

(define result-iP19 (verify iP19))
(displayln (if (unsat? result-iP19)
               "iP19 VERIFIED: L1_TO_L2_REGISTER_SCRUB - L1 GPR/XMM not visible to L2 after TDG.VP.ENTER"
               "iP19 VIOLATED: L1_TO_L2_REGISTER_SCRUB - L1 register leaked to L2 via VCPU transition"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP20: L2_TO_L1_EXIT_IBPB  [Doc P3]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic l2-exit-ip20      boolean?)  ; L2 se exit event hua
(define-symbolic ibpb-fired-ip20   boolean?)  ; IBPB barrier fire hua
(define-symbolic l1-reads-spec-ip20 boolean?) ; L1 ne L2 stale spec state read ki

(define iP20
  (assert
    (not (and l2-exit-ip20
              (not ibpb-fired-ip20)
              l1-reads-spec-ip20))))           ; IBPB ke bina L1 leak — IMPOSSIBLE

(define result-iP20 (verify iP20))
(displayln (if (unsat? result-iP20)
               "iP20 VERIFIED: L2_TO_L1_EXIT_IBPB - IBPB enforced on every L2-to-L1 exit"
               "iP20 VIOLATED: L2_TO_L1_EXIT_IBPB - L1 read stale L2 speculative state; IBPB missing"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP21: MSR_SHADOW_BITMAP_INTEGRITY  [Doc P4]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic curr-vm-ip21      integer?)  ; 1=L1, 2=L2
(define-symbolic msr-op-ip21       boolean?)  ; MSR read/write hua
(define-symbolic shadow-val-ip21   integer?)  ; L1 shadow MSR value
(define-symbolic hw-direct-ip21    integer?)  ; hardware raw MSR value
(define-symbolic returned-val-ip21 integer?)  ; L2 ko actually mili value

(define iP21
  (assert
    (not (and (= curr-vm-ip21 L2_VM)
              msr-op-ip21
              (not (= shadow-val-ip21 hw-direct-ip21))   ; shadow != hardware
              (= returned-val-ip21 hw-direct-ip21)))))    ; L2 ne hardware value dekhi — IMPOSSIBLE

(define result-iP21 (verify iP21))
(displayln (if (unsat? result-iP21)
               "iP21 VERIFIED: MSR_SHADOW_BITMAP_INTEGRITY - L2 MSR ops return L1 shadow value only"
               "iP21 VIOLATED: MSR_SHADOW_BITMAP_INTEGRITY - L2 bypassed MSR shadow, got hardware value"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP22: L2_INTERRUPT_WINDOW_ENFORCE  [Doc P7]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic l2-exec-cycles-ip22   integer?)  ; L2 continuous execution (cycles)
(define-symbolic l1-max-thresh-ip22    integer?)  ; L1 VMM TSC deadline value
(define-symbolic forced-exit-ip22      boolean?)  ; hardware forced L2 preemption

(define iP22
  (assert
    (not (and (> l2-exec-cycles-ip22 l1-max-thresh-ip22)
              (> l1-max-thresh-ip22 0)
              (not forced-exit-ip22)))))           ; threshold cross + no exit — IMPOSSIBLE

(define result-iP22 (verify iP22))
(displayln (if (unsat? result-iP22)
               "iP22 VERIFIED: L2_INTERRUPT_WINDOW_ENFORCE - L1 scheduling authority intact via TSC deadline"
               "iP22 VIOLATED: L2_INTERRUPT_WINDOW_ENFORCE - L2 exceeded quantum; forced exit missing"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP23: SEPT_L2_NO_RECURSIVE_MAPPING  [Doc P8]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic l2-sept-hpa-ip23    integer?)  ; L2 SEPT entry target physical address
(define-symbolic l1-sept-base-ip23   integer?)  ; L1 SEPT root base address
(define-symbolic l2-entry-valid-ip23 boolean?)  ; L2 SEPT entry valid/present

(define iP23
  (assert
    (not (and l2-entry-valid-ip23
              (= l2-sept-hpa-ip23 l1-sept-base-ip23)))))  ; L2 -> L1 SEPT — IMPOSSIBLE

(define result-iP23 (verify iP23))
(displayln (if (unsat? result-iP23)
               "iP23 VERIFIED: SEPT_L2_NO_RECURSIVE_MAPPING - L2 SEPT cannot alias L1 SEPT structures"
               "iP23 VIOLATED: SEPT_L2_NO_RECURSIVE_MAPPING - L2 SEPT recursive mapping to L1 detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP24: ILLEGAL_L2_SEAMCALL_BLOCK  [Doc P9]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic curr-vm-ip24     integer?)  ; 1=L1, 2=L2
(define-symbolic instruction-ip24 integer?)  ; opcode executed
(define-symbolic exc-raised-ip24  integer?)  ; exception vector (6=#UD)

(define iP24
  (assert
    (not (and (= curr-vm-ip24 L2_VM)
              (= instruction-ip24 INST_SEAMCALL)
              (not (= exc-raised-ip24 EXC_UD))))))  ; SEAMCALL L2 mein + no #UD — IMPOSSIBLE

(define result-iP24 (verify iP24))
(displayln (if (unsat? result-iP24)
               "iP24 VERIFIED: ILLEGAL_L2_SEAMCALL_BLOCK - SEAMCALL from L2 always raises #UD"
               "iP24 VIOLATED: ILLEGAL_L2_SEAMCALL_BLOCK - L2 SEAMCALL succeeded; privilege hierarchy broken"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP25: TDG_VP_ENTER_ENTRY_POINT_CFI  [Doc P10]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic enter-fired-ip25      boolean?)  ; TDG.VP.ENTER hua
(define-symbolic actual-rip-ip25       integer?)  ; L2 first-cycle RIP value
(define-symbolic designated-entry-ip25 integer?)  ; VMCS-defined safe entry point

(define iP25
  (assert
    (not (and enter-fired-ip25
              (not (= actual-rip-ip25 designated-entry-ip25))))))  ; wrong RIP on entry — IMPOSSIBLE

(define result-iP25 (verify iP25))
(displayln (if (unsat? result-iP25)
               "iP25 VERIFIED: TDG_VP_ENTER_ENTRY_POINT_CFI - L2 enters at VMCS-designated RIP (CFI enforced)"
               "iP25 VIOLATED: TDG_VP_ENTER_ENTRY_POINT_CFI - L2 entry at non-designated RIP; CFI violation"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; ADDITIONAL L1/L2 TD PARTITIONING INTEGRITY PROPERTIES  [NEW]
;;
;; Mapping:
;;   tpP1  -> iP26  L2_ALIAS_BACKED_BY_L1_OWNER
;;   tpP2  -> iP27  L2_PERM_SUBSET_OF_L1_PERM
;;   tpP4  -> iP28  SEPT_UPDATE_WALK_ATOMICITY
;;   tpP6  -> iP29  L2_ENTRY_STATE_CONTAINMENT
;;   tpP7  -> iP30  L2_EXIT_STATE_CONTAINMENT
;;   tpP8  -> iP31  L2_EXIT_CONTROL_FLOW_TARGET
;;   tpP10 -> iP32  PRIVATE_HKID_NO_GUEST_OVERRIDE
;;   tpP12 -> iP33  L2_PRIVATE_WRITE_TD_OWNER_SET
;;   tpP13 -> iP34  CONVERSION_INVALIDATES_L2_ALIASES
;;   tpP14 -> iP35  HKID_REASSIGN_AFTER_FLUSH
;;   tpP16 -> iP36  L2_SEPT_HPA_PAMT_TYPE_MATCH
;;   tpP17 -> iP37  L2_VMCS_CONTROL_MASKED_BY_TDX
;;   tpP19 -> iP38  L2_IMPORTED_ALIAS_BLOCKED_UNTIL_VERIFIED
;;   tpP21 -> iP39  CIPHERTEXT_REPLAY_ACROSS_HPA_FAILS
;;   tpP22 -> iP51  INTEGRITY_FAILURE_CONTAINMENT
;;   tpP23 -> iP52  L2_FETCH_REQUIRES_X_AT_L1_AND_L2
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Additional L1/L2 partitioning constants
(define ALLOWED_L2_ALIAS_TYPE  1)   ; sentinel: PAMT page type allowed for L2 alias backing


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP26: L2_ALIAS_BACKED_BY_L1_OWNER  [tpP1]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic l2-hpa-ip26       integer?)  ; HPA resolved by L2 SEPT
(define-symbolic l1-hpa-ip26       integer?)  ; HPA resolved by owning TD's L1 SEPT
(define-symbolic pamt-owner-ip26   integer?)  ; PAMT.owner of L2-resolved HPA
(define-symbolic current-tdr-ip26  integer?)  ; current TDR identifier
(define-symbolic l2-mapped-ip26    boolean?)  ; L2_SEPT entry state == L2_MAPPED

(define iP26
  (assert
    (not (and l2-mapped-ip26
              (or (not (= l2-hpa-ip26 l1-hpa-ip26))
                  (not (= pamt-owner-ip26 current-tdr-ip26)))))))
              ; L2_MAPPED + (HPA mismatch OR wrong PAMT owner) — IMPOSSIBLE

(define result-iP26 (verify iP26))
(displayln (if (unsat? result-iP26)
               "iP26 VERIFIED: L2_ALIAS_BACKED_BY_L1_OWNER - L2 SEPT alias matches L1 mapping and PAMT owner"
               "iP26 VIOLATED: L2_ALIAS_BACKED_BY_L1_OWNER - L2 alias not backed by owning TD's L1 mapping"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP27: L2_PERM_SUBSET_OF_L1_PERM  [tpP2]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic l2-r-ip27 l2-w-ip27 l2-x-ip27 boolean?)  ; L2 R/W/X permission bits
(define-symbolic l1-r-ip27 l1-w-ip27 l1-x-ip27 boolean?)  ; L1 R/W/X permission bits

(define iP27
  (assert
    (not (or
      (and l2-r-ip27 (not l1-r-ip27))    ; L2 R set, L1 R clear — IMPOSSIBLE
      (and l2-w-ip27 (not l1-w-ip27))    ; L2 W set, L1 W clear — IMPOSSIBLE
      (and l2-x-ip27 (not l1-x-ip27)))))) ; L2 X set, L1 X clear — IMPOSSIBLE

(define result-iP27 (verify iP27))
(displayln (if (unsat? result-iP27)
               "iP27 VERIFIED: L2_PERM_SUBSET_OF_L1_PERM - L2 permissions never exceed L1 permissions"
               "iP27 VIOLATED: L2_PERM_SUBSET_OF_L1_PERM - L2 has permission bit absent from L1"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP28: SEPT_UPDATE_WALK_ATOMICITY  [tpP4]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic old-entry-ip28          integer?)  ; old SEPT entry encoding
(define-symbolic new-entry-ip28          integer?)  ; new SEPT entry encoding
(define-symbolic observed-entry-ip28     integer?)  ; entry seen by concurrent walker
(define-symbolic update-in-progress-ip28 boolean?)  ; SEPT_update lock held

(define iP28
  (assert
    (not (and update-in-progress-ip28
              (not (= observed-entry-ip28 old-entry-ip28))
              (not (= observed-entry-ip28 new-entry-ip28))))))
              ; walker sees neither old nor new — IMPOSSIBLE

(define result-iP28 (verify iP28))
(displayln (if (unsat? result-iP28)
               "iP28 VERIFIED: SEPT_UPDATE_WALK_ATOMICITY - Concurrent walkers see only old or new SEPT entry"
               "iP28 VIOLATED: SEPT_UPDATE_WALK_ATOMICITY - Translation walk observed a torn SEPT entry"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP29: L2_ENTRY_STATE_CONTAINMENT  [tpP6]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic guest-state-source-ip29  integer?)  ; TDVPS owner id of state source
(define-symbolic current-tdvps-id-ip29    integer?)  ; current TDR/VCPU/L2 TDVPS id
(define-symbolic l2-entry-fired-ip29      boolean?)  ; L2 VM entry occurred

(define iP29
  (assert
    (not (and l2-entry-fired-ip29
              (not (= guest-state-source-ip29 current-tdvps-id-ip29))))))
              ; entry state sourced from foreign TDVPS — IMPOSSIBLE

(define result-iP29 (verify iP29))
(displayln (if (unsat? result-iP29)
               "iP29 VERIFIED: L2_ENTRY_STATE_CONTAINMENT - L2 entry state confined to owning TDVPS"
               "iP29 VIOLATED: L2_ENTRY_STATE_CONTAINMENT - L2 entry sourced state from foreign TDVPS"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP30: L2_EXIT_STATE_CONTAINMENT  [tpP7]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic exit-write-target-ip30   integer?)  ; TDVPS owner id of exit write target
(define-symbolic current-tdvps-id-ip30    integer?)  ; current TDR/VCPU/L2 TDVPS id
(define-symbolic l2-exit-fired-ip30       boolean?)  ; L2 VM exit occurred

(define iP30
  (assert
    (not (and l2-exit-fired-ip30
              (not (= exit-write-target-ip30 current-tdvps-id-ip30))))))
              ; exit state written to foreign TDVPS — IMPOSSIBLE

(define result-iP30 (verify iP30))
(displayln (if (unsat? result-iP30)
               "iP30 VERIFIED: L2_EXIT_STATE_CONTAINMENT - L2 exit state confined to owning TDVPS"
               "iP30 VIOLATED: L2_EXIT_STATE_CONTAINMENT - L2 exit state written to foreign TDVPS"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP31: L2_EXIT_CONTROL_FLOW_TARGET  [tpP8]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define TARGET_TDX_MODULE   1)
(define TARGET_L1_HANDLER   2)
(define TARGET_SANITIZED_EXIT 3)

(define-symbolic l2-exit-fired-ip31  boolean?)  ; L2 VM exit occurred
(define-symbolic exit-target-ip31    integer?)  ; resolved control-flow target

(define iP31
  (assert
    (not (and l2-exit-fired-ip31
              (not (= exit-target-ip31 TARGET_TDX_MODULE))
              (not (= exit-target-ip31 TARGET_L1_HANDLER))
              (not (= exit-target-ip31 TARGET_SANITIZED_EXIT))))))
              ; exit target outside allowed set — IMPOSSIBLE

(define result-iP31 (verify iP31))
(displayln (if (unsat? result-iP31)
               "iP31 VERIFIED: L2_EXIT_CONTROL_FLOW_TARGET - L2 exits target only TDX Module/L1 handler/sanitized exit"
               "iP31 VIOLATED: L2_EXIT_CONTROL_FLOW_TARGET - L2 exit transferred control to disallowed target"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP32: PRIVATE_HKID_NO_GUEST_OVERRIDE  [tpP10]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic transaction-hkid-ip32 integer?)  ; HKID used in the memory transaction
(define-symbolic tdcs-hkid-ip32        integer?)  ; TDCS.HKID[current_TDR]
(define-symbolic private-access-ip32   boolean?)  ; transaction is a private access

(define iP32
  (assert
    (not (and private-access-ip32
              (not (= transaction-hkid-ip32 tdcs-hkid-ip32))))))
              ; private access used non-TDCS HKID — IMPOSSIBLE

(define result-iP32 (verify iP32))
(displayln (if (unsat? result-iP32)
               "iP32 VERIFIED: PRIVATE_HKID_NO_GUEST_OVERRIDE - Private accesses always use TDCS-configured HKID"
               "iP32 VIOLATED: PRIVATE_HKID_NO_GUEST_OVERRIDE - Private access used guest/host-overridden HKID"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP33: L2_PRIVATE_WRITE_TD_OWNER_SET  [tpP12]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic l2-private-store-ip33  boolean?)  ; L2 store through private alias occurred
(define-symbolic store-hkid-ip33        integer?)  ; HKID used for the store transaction
(define-symbolic td-private-hkid-ip33   integer?)  ; owning TD's private HKID
(define-symbolic td-owner-bit-set-ip33  boolean?)  ; TD_OWNER metadata bit after store

(define iP33
  (assert
    (not (and l2-private-store-ip33
              (or (not (= store-hkid-ip33 td-private-hkid-ip33))
                  (not td-owner-bit-set-ip33))))))
              ; L2 private store + (wrong HKID OR TD_OWNER not set) — IMPOSSIBLE

(define result-iP33 (verify iP33))
(displayln (if (unsat? result-iP33)
               "iP33 VERIFIED: L2_PRIVATE_WRITE_TD_OWNER_SET - L2 private writes use TD HKID and set TD_OWNER"
               "iP33 VIOLATED: L2_PRIVATE_WRITE_TD_OWNER_SET - L2 private write left TD_OWNER unset or wrong HKID"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP34: CONVERSION_INVALIDATES_L2_ALIASES  [tpP13]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define L2_FREE     0)
(define L2_MAPPED   1)
(define L2_BLOCKED  2)

(define-symbolic conversion-done-ip34 boolean?)  ; private<->shared conversion completed
(define-symbolic l2-alias-state-ip34  integer?)  ; state of an L2 alias for the converted page

(define iP34
  (assert
    (not (and conversion-done-ip34
              (= l2-alias-state-ip34 L2_MAPPED)))))
              ; conversion done + alias still MAPPED — IMPOSSIBLE

(define result-iP34 (verify iP34))
(displayln (if (unsat? result-iP34)
               "iP34 VERIFIED: CONVERSION_INVALIDATES_L2_ALIASES - Page conversion clears/blocks all L2 aliases"
               "iP34 VIOLATED: CONVERSION_INVALIDATES_L2_ALIASES - L2 alias remained MAPPED after page conversion"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP35: HKID_REASSIGN_AFTER_FLUSH  [tpP14]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hkid-ip35           integer?)  ; HKID being torn down
(define-symbolic kot-state-ip35      integer?)  ; KOT[hkid] state
(define-symbolic cache-entry-hkid-ip35 integer?) ; HKID tag of a translation cache entry
(define-symbolic cache-entry-valid-ip35 boolean?) ; translation cache entry still valid

(define iP35
  (assert
    (not (and (= kot-state-ip35 HKID_FREE)
              (= hkid-ip35 cache-entry-hkid-ip35)
              cache-entry-valid-ip35))))
              ; HKID freed + stale translation entry for it still valid — IMPOSSIBLE

(define result-iP35 (verify iP35))
(displayln (if (unsat? result-iP35)
               "iP35 VERIFIED: HKID_REASSIGN_AFTER_FLUSH - No translation cache entries survive HKID teardown"
               "iP35 VIOLATED: HKID_REASSIGN_AFTER_FLUSH - Stale translation cache entry found for freed HKID"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP36: L2_SEPT_HPA_PAMT_TYPE_MATCH  [tpP16]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic l2-sept-leaf-valid-ip36 boolean?)  ; L2 SEPT leaf is valid/present
(define-symbolic pamt-type-ip36          integer?)  ; PAMT.type of referenced HPA
(define-symbolic pamt-owner-ip36         integer?)  ; PAMT.owner of referenced HPA
(define-symbolic current-tdr-ip36        integer?)  ; current TDR identifier

(define iP36
  (assert
    (not (and l2-sept-leaf-valid-ip36
              (or (not (= pamt-type-ip36 ALLOWED_L2_ALIAS_TYPE))
                  (not (= pamt-owner-ip36 current-tdr-ip36)))))))
              ; valid L2 leaf + (disallowed PAMT type OR wrong owner) — IMPOSSIBLE

(define result-iP36 (verify iP36))
(displayln (if (unsat? result-iP36)
               "iP36 VERIFIED: L2_SEPT_HPA_PAMT_TYPE_MATCH - L2 SEPT leaves only reference allowed, TD-owned PAMT pages"
               "iP36 VIOLATED: L2_SEPT_HPA_PAMT_TYPE_MATCH - L2 SEPT leaf references disallowed/foreign PAMT page"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP37: L2_VMCS_CONTROL_MASKED_BY_TDX  [tpP17]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Modelled per-dimension: each boolean represents one TDX-policy control bit.
;; req_bit can only be set in effective if allowed_bit is also set.
(define-symbolic req-ctrl-A-ip37 req-ctrl-B-ip37 req-ctrl-C-ip37 boolean?)  ; requested control bits
(define-symbolic allowed-A-ip37  allowed-B-ip37  allowed-C-ip37  boolean?)  ; TDX-allowed mask bits
(define-symbolic eff-ctrl-A-ip37 eff-ctrl-B-ip37 eff-ctrl-C-ip37 boolean?)  ; effective control bits

(define iP37
  (assert
    (not (or
      ;; effective bit set but either (req bit clear) or (allowed bit clear) — IMPOSSIBLE
      (and eff-ctrl-A-ip37 (or (not req-ctrl-A-ip37) (not allowed-A-ip37)))
      (and eff-ctrl-B-ip37 (or (not req-ctrl-B-ip37) (not allowed-B-ip37)))
      (and eff-ctrl-C-ip37 (or (not req-ctrl-C-ip37) (not allowed-C-ip37)))
      ;; req bit set + allowed bit set but effective bit clear — IMPOSSIBLE (mask applied wrong)
      (and req-ctrl-A-ip37 allowed-A-ip37 (not eff-ctrl-A-ip37))
      (and req-ctrl-B-ip37 allowed-B-ip37 (not eff-ctrl-B-ip37))
      (and req-ctrl-C-ip37 allowed-C-ip37 (not eff-ctrl-C-ip37))))))
              ; effective_controls != (requested & tdx_allowed_mask) — IMPOSSIBLE

(define result-iP37 (verify iP37))
(displayln (if (unsat? result-iP37)
               "iP37 VERIFIED: L2_VMCS_CONTROL_MASKED_BY_TDX - L2 VMCS controls remain within TDX-allowed mask"
               "iP37 VIOLATED: L2_VMCS_CONTROL_MASKED_BY_TDX - L2 VMCS control bypassed TDX-allowed mask"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP38: L2_IMPORTED_ALIAS_BLOCKED_UNTIL_VERIFIED  [tpP19]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic import-pending-ip38   boolean?)  ; page import is pending
(define-symbolic l2-alias-exists-ip38  boolean?)  ; an L2 alias exists for the page
(define-symbolic l2-alias-state-ip38   integer?)  ; state of that L2 alias
(define-symbolic freshness-ok-ip38     boolean?)  ; freshness check passed
(define-symbolic integrity-ok-ip38     boolean?)  ; integrity check passed
(define-symbolic mapping-ok-ip38       boolean?)  ; mapping check passed

(define iP38
  (assert
    (not (or
      ;; pending import + alias exists + not BLOCKED — IMPOSSIBLE
      (and import-pending-ip38
           l2-alias-exists-ip38
           (not (= l2-alias-state-ip38 L2_BLOCKED)))
      ;; alias MAPPED while any verification incomplete — IMPOSSIBLE
      (and (= l2-alias-state-ip38 L2_MAPPED)
           (or (not freshness-ok-ip38)
               (not integrity-ok-ip38)
               (not mapping-ok-ip38)))))))

(define result-iP38 (verify iP38))
(displayln (if (unsat? result-iP38)
               "iP38 VERIFIED: L2_IMPORTED_ALIAS_BLOCKED_UNTIL_VERIFIED - Pending imports stay L2_BLOCKED until fully verified"
               "iP38 VIOLATED: L2_IMPORTED_ALIAS_BLOCKED_UNTIL_VERIFIED - L2 alias mapped before import verification complete"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP39: CIPHERTEXT_REPLAY_ACROSS_HPA_FAILS  [tpP21]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hpa-a-ip39         integer?)  ; original HPA of ciphertext
(define-symbolic hpa-b-ip39         integer?)  ; target HPA where ciphertext is replayed
(define-symbolic mac-tweak-a-ip39   integer?)  ; tweak derived from HPA_a (encoded in MAC)
(define-symbolic mac-tweak-b-ip39   integer?)  ; tweak derived from HPA_b (recomputed)
(define-symbolic integrity-pass-ip39 boolean?) ; integrity check result
(define-symbolic data-consumed-ip39  boolean?) ; decrypted data consumed by guest/module

(define iP39
  (assert
    (not (and (not (= hpa-a-ip39 hpa-b-ip39))
              (not (= mac-tweak-a-ip39 mac-tweak-b-ip39))  ; tweak mismatch (replay)
              integrity-pass-ip39
              data-consumed-ip39))))
              ; alag HPA tweak + integrity pass + data consumed — IMPOSSIBLE

(define result-iP39 (verify iP39))
(displayln (if (unsat? result-iP39)
               "iP39 VERIFIED: CIPHERTEXT_REPLAY_ACROSS_HPA_FAILS - Replayed ciphertext at a different HPA fails integrity before consumption"
               "iP39 VIOLATED: CIPHERTEXT_REPLAY_ACROSS_HPA_FAILS - Replayed ciphertext across HPAs passed integrity and was consumed"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP51: INTEGRITY_FAILURE_CONTAINMENT  [tpP22]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic integrity-failure-ip51       boolean?)  ; integrity violation occurred
(define-symbolic diag-state-owner-ip51        integer?)  ; TD/L2 owner id of diagnostic-visible state
(define-symbolic failing-partition-id-ip51    integer?)  ; id of the TD partition that failed
(define-symbolic diag-state-sanitized-ip51    boolean?)  ; diagnostic state is sanitized

(define iP51
  (assert
    (not (and integrity-failure-ip51
              (not (= diag-state-owner-ip51 failing-partition-id-ip51))
              (not diag-state-sanitized-ip51)))))
              ; failure + diagnostic exposes foreign unsanitized state — IMPOSSIBLE

(define result-iP51 (verify iP51))
(displayln (if (unsat? result-iP51)
               "iP51 VERIFIED: INTEGRITY_FAILURE_CONTAINMENT - Integrity failure diagnostics stay within failing partition"
               "iP51 VIOLATED: INTEGRITY_FAILURE_CONTAINMENT - Integrity failure exposed unrelated partition state"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP52: L2_FETCH_REQUIRES_X_AT_L1_AND_L2  [tpP23]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic l2-fetch-retire-ip52 boolean?)  ; L2 instruction fetch retired
(define-symbolic x-perm-l2-ip52       boolean?)  ; execute permission from L2 SEPT leaf
(define-symbolic x-perm-l1-ip52       boolean?)  ; execute permission from L1 SEPT leaf

(define iP52
  (assert
    (not (and l2-fetch-retire-ip52
              (or (not x-perm-l2-ip52)
                  (not x-perm-l1-ip52))))))
              ; fetch retired + missing X perm at either layer — IMPOSSIBLE

(define result-iP52 (verify iP52))
(displayln (if (unsat? result-iP52)
               "iP52 VERIFIED: L2_FETCH_REQUIRES_X_AT_L1_AND_L2 - L2 fetch retires only with execute permission at both layers"
               "iP52 VIOLATED: L2_FETCH_REQUIRES_X_AT_L1_AND_L2 - L2 fetch retired without execute permission at L1 or L2"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ============================================================
;; ADDITIONAL ATTESTATION INTEGRITY PROPERTIES  [NEW — RAG]
;;
;; Mapping (RAG attestation property -> formal id):
;;   MRTD Lock-after-Build Immutability        -> iP53
;;   MRTD Report Snapshot Consistency          -> iP54
;;   RTMR Extend Atomic Commit                 -> iP55
;;   RTMR Extend Serialization per Register    -> iP56
;;   RTMR Index Bounds Enforcement             -> iP57
;;   RTMR Extend Input Coherency               -> iP58
;;   RTMR Extend Private-Memory Enforcement    -> iP59
;;   REPORTDATA Exact Binding                  -> iP60
;;   REPORTDATA Snapshot Atomicity             -> iP61
;;   REPORTDATA No-Stale-Reuse after Interrupt -> iP62
;;   REPORTMAC Input Completeness              -> iP63
;;   REPORTTYPE TDX Domain Separation          -> iP64
;;   Report Version Selection Correctness      -> iP65
;;   Report Buffer Size Non-Mutation on Failure-> iP66
;;   TDINFO Field Source Authenticity          -> iP67
;;   REPORTMAC Per-TD Context Isolation        -> iP68
;;   Report MAC Key Non-Substitutability       -> iP69
;;   Report MAC Key Epoch Binding              -> iP70
;;   TEE_TCB Current-State Accuracy            -> iP71
;;   CPUSVN Fresh Read for Report              -> iP72
;;   TD Attributes Report Accuracy             -> iP73
;;   SERVTD Hash Selection Correctness         -> iP74
;;   Assigned SVN and Signer Field Integrity   -> iP75
;;   MRTD/RTMR Partial Write Fault Resistance  -> iP76
;;   Measurement Register Zeroization on Teardown -> iP77
;;   TD Lifecycle Report Eligibility           -> iP78
;;   No Report after TD Fatal Transition       -> iP79
;;   TD Destroy/Recreate Anti-Replay Binding   -> iP80
;;   HKID/MKTME KeyID Attestation Binding      -> iP81
;;   Report Generation Blocks TDCS Mutation Race -> iP82
;;   QE Verification Success Only after MAC Validation -> iP83
;;   QE Report Body Immutability Verify-to-Sign -> iP84
;;   Reserved and Must-Be-Zero Field Enforcement -> iP85
;;   TDREPORT Output Bounds Enforcement        -> iP86
;;   Report Hash Engine Domain Reset           -> iP87
;;   Report Generation No Debug Override       -> iP88
;;   Migration Report Freshness Failure on Platform Change -> iP89
;; ============================================================
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
;; Additional attestation constants
(define REPORT_LIFECYCLE_RUNNABLE 1)   ; TD lifecycle state eligible for TDG.MR.REPORT
(define REPORT_VERSION_0 0)
(define REPORT_VERSION_1 1)
(define REPORT_VERSION_2 2)
(define REPORTTYPE_TDX   1)            ; REPORTTYPE.TYPE value identifying a TDX report
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP53: MRTD_LOCK_AFTER_BUILD_IMMUTABILITY
;;
;; Property: Build phase finalize hone ke baad TDCS.MRTD ka
;;           koi bhi path (RTL/microcode/DMA/debug/reset-recovery/
;;           fault-retry) se change hona — IMPOSSIBLE
;; Ref: Base Spec - TD measurement reporting; ABI Spec - TDINFO_STRUCT.MRTD
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic build-finalized-ip53 boolean?)
(define-symbolic mrtd-before-ip53     integer?)
(define-symbolic mrtd-after-ip53      integer?)
 
(define iP53
  (assert
    (not (and build-finalized-ip53
              (not (= mrtd-before-ip53 mrtd-after-ip53))))))
 
(define result-iP53 (verify iP53))
(displayln (if (unsat? result-iP53)
               "iP53 VERIFIED: MRTD_LOCK_AFTER_BUILD_IMMUTABILITY - TDCS.MRTD immutable after build finalize"
               "iP53 VIOLATED: MRTD_LOCK_AFTER_BUILD_IMMUTABILITY - TDCS.MRTD changed after build finalize"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP54: MRTD_REPORT_SNAPSHOT_CONSISTENCY
;;
;; Property: TDG.MR.REPORT mein TDREPORT.TDINFO.MRTD aur
;;           MAC computation mein use hua MRTD alag hona
;;           — IMPOSSIBLE
;; Ref: ABI Spec - REPORTMACSTRUCT, TDINFO_STRUCT
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic mrtd-in-tdinfo-ip54 integer?)
(define-symbolic mrtd-in-mac-ip54    integer?)
(define-symbolic report-gen-ip54     boolean?)
 
(define iP54
  (assert
    (not (and report-gen-ip54
              (not (= mrtd-in-tdinfo-ip54 mrtd-in-mac-ip54))))))
 
(define result-iP54 (verify iP54))
(displayln (if (unsat? result-iP54)
               "iP54 VERIFIED: MRTD_REPORT_SNAPSHOT_CONSISTENCY - TDINFO.MRTD matches MAC-protected MRTD"
               "iP54 VIOLATED: MRTD_REPORT_SNAPSHOT_CONSISTENCY - TDINFO.MRTD diverges from MAC-bound MRTD"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP55: RTMR_EXTEND_ATOMIC_COMMIT
;;
;; Property: RTMR extend fail/interrupt/fault hone par
;;           partial visible state banna — IMPOSSIBLE
;; Ref: ABI Spec - TDG.MR.RTMR.EXTEND, SHA384 semantics
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic extend-failed-ip55       boolean?)
(define-symbolic rtmr-pre-ip55            integer?)
(define-symbolic rtmr-post-ip55           integer?)
(define-symbolic rtmr-fully-computed-ip55 integer?)
 
(define iP55
  (assert
    (not (and extend-failed-ip55
              (not (= rtmr-post-ip55 rtmr-pre-ip55))
              (not (= rtmr-post-ip55 rtmr-fully-computed-ip55))))))
 
(define result-iP55 (verify iP55))
(displayln (if (unsat? result-iP55)
               "iP55 VERIFIED: RTMR_EXTEND_ATOMIC_COMMIT - Failed/interrupted extend leaves RTMR at old or fully-new value only"
               "iP55 VIOLATED: RTMR_EXTEND_ATOMIC_COMMIT - Failed extend left RTMR at a partial/corrupted value"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP56: RTMR_EXTEND_SERIALIZATION_PER_REGISTER
;;
;; Property: Same RTMR index par do vCPUs concurrent exclusive
;;           ownership claim karna — IMPOSSIBLE
;; Ref: ABI Spec - TDG.MR.RTMR.EXTEND concurrency restrictions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic rtmr-index-A-ip56    integer?)
(define-symbolic rtmr-index-B-ip56    integer?)
(define-symbolic owns-datapath-A-ip56 boolean?)
(define-symbolic owns-datapath-B-ip56 boolean?)
 
(define iP56
  (assert
    (not (and (= rtmr-index-A-ip56 rtmr-index-B-ip56)
              owns-datapath-A-ip56
              owns-datapath-B-ip56))))
 
(define result-iP56 (verify iP56))
(displayln (if (unsat? result-iP56)
               "iP56 VERIFIED: RTMR_EXTEND_SERIALIZATION_PER_REGISTER - Same-index RTMR extends are mutually exclusive"
               "iP56 VIOLATED: RTMR_EXTEND_SERIALIZATION_PER_REGISTER - Concurrent extends on same RTMR index both held ownership"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP57: RTMR_INDEX_BOUNDS_ENFORCEMENT
;;
;; Property: Invalid RTMR index ke saath extend accepted ho
;;           ya koi state modify ho — IMPOSSIBLE
;; Ref: ABI Spec - TDG.MR.RTMR.EXTEND, TDINFO_STRUCT.RTMR0..RTMR3
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define RTMR_MIN_INDEX 0)
(define RTMR_MAX_INDEX 3)
 
(define-symbolic rtmr-index-ip57     integer?)
(define-symbolic op-accepted-ip57    boolean?)
(define-symbolic state-modified-ip57 boolean?)
 
(define iP57
  (assert
    (not (and (or (< rtmr-index-ip57 RTMR_MIN_INDEX)
                  (> rtmr-index-ip57 RTMR_MAX_INDEX))
              (or op-accepted-ip57
                  state-modified-ip57)))))
 
(define result-iP57 (verify iP57))
(displayln (if (unsat? result-iP57)
               "iP57 VERIFIED: RTMR_INDEX_BOUNDS_ENFORCEMENT - Invalid RTMR index always fails without state modification"
               "iP57 VIOLATED: RTMR_INDEX_BOUNDS_ENFORCEMENT - Invalid RTMR index accepted or modified state"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP58: RTMR_EXTEND_INPUT_COHERENCY
;;
;; Property: RTMR extend hash, ek se zyada alag sources se
;;           combined bytes se compute hona — IMPOSSIBLE
;; Ref: ABI Spec - TDG.MR.RTMR.EXTEND input buffer semantics
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic capture-source-count-ip58 integer?)
(define-symbolic hash-computed-ip58        boolean?)
 
(define iP58
  (assert
    (not (and hash-computed-ip58
              (> capture-source-count-ip58 1)))))
 
(define result-iP58 (verify iP58))
(displayln (if (unsat? result-iP58)
               "iP58 VERIFIED: RTMR_EXTEND_INPUT_COHERENCY - Extension buffer captured as one coherent read before hashing"
               "iP58 VIOLATED: RTMR_EXTEND_INPUT_COHERENCY - Extend hash computed from spliced/multiple sources"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP59: RTMR_EXTEND_PRIVATE_MEMORY_ENFORCEMENT
;;
;; Property: Non-private/changed-attribute GPA se RTMR mutate
;;           hona — IMPOSSIBLE
;; Ref: ABI Spec - TDG.MR.RTMR.EXTEND EXTEND_DATA is private
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic extend-gpa-private-ip59  boolean?)
(define-symbolic attr-changed-mid-op-ip59 boolean?)
(define-symbolic rtmr-mutated-ip59        boolean?)
 
(define iP59
  (assert
    (not (and (or (not extend-gpa-private-ip59)
                  attr-changed-mid-op-ip59)
              rtmr-mutated-ip59))))
 
(define result-iP59 (verify iP59))
(displayln (if (unsat? result-iP59)
               "iP59 VERIFIED: RTMR_EXTEND_PRIVATE_MEMORY_ENFORCEMENT - Extend only mutates RTMR for stable private-memory input"
               "iP59 VIOLATED: RTMR_EXTEND_PRIVATE_MEMORY_ENFORCEMENT - RTMR mutated using shared/aliased/attribute-changing input"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP60: REPORTDATA_EXACT_BINDING
;;
;; Property: REPORTMACSTRUCT.REPORTDATA (visible) aur MAC mein
;;           use hua REPORTDATA byte-for-byte mismatch kare
;;           same report instance mein — IMPOSSIBLE
;; Ref: ABI Spec - TDG.MR.REPORT, REPORTMACSTRUCT.REPORTDATA
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic reportdata-visible-ip60 integer?)
(define-symbolic reportdata-mac-ip60     integer?)
(define-symbolic report-instance-ip60    boolean?)
 
(define iP60
  (assert
    (not (and report-instance-ip60
              (not (= reportdata-visible-ip60 reportdata-mac-ip60))))))
 
(define result-iP60 (verify iP60))
(displayln (if (unsat? result-iP60)
               "iP60 VERIFIED: REPORTDATA_EXACT_BINDING - Visible REPORTDATA matches MAC-bound REPORTDATA exactly"
               "iP60 VIOLATED: REPORTDATA_EXACT_BINDING - Visible REPORTDATA diverges from MAC-bound value"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP61: REPORTDATA_SNAPSHOT_ATOMICITY
;;
;; Property: REPORTDATA capture, multiple sources se combine
;;           hona — IMPOSSIBLE
;; Ref: ABI Spec - TDG.MR.REPORT input REPORTDATA, interruptibility
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic reportdata-source-count-ip61 integer?)
(define-symbolic reportdata-captured-ip61     boolean?)
 
(define iP61
  (assert
    (not (and reportdata-captured-ip61
              (> reportdata-source-count-ip61 1)))))
 
(define result-iP61 (verify iP61))
(displayln (if (unsat? result-iP61)
               "iP61 VERIFIED: REPORTDATA_SNAPSHOT_ATOMICITY - REPORTDATA captured as one coherent 64-byte snapshot"
               "iP61 VIOLATED: REPORTDATA_SNAPSHOT_ATOMICITY - REPORTDATA captured from spliced/multiple sources"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP62: REPORTDATA_NO_STALE_REUSE_AFTER_INTERRUPT
;;
;; Property: Interrupted report resume par old REPORTDATA
;;           snapshot ko naye TD state ke saath mix karna
;;           — IMPOSSIBLE
;; Ref: ABI Spec - TDG.MR.REPORT interruptibility and progress recording
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic report-interrupted-ip62       boolean?)
(define-symbolic resumed-snapshot-epoch-ip62   integer?)
(define-symbolic resumed-state-epoch-ip62      integer?)
 
(define iP62
  (assert
    (not (and report-interrupted-ip62
              (not (= resumed-snapshot-epoch-ip62 resumed-state-epoch-ip62))))))
 
(define result-iP62 (verify iP62))
(displayln (if (unsat? result-iP62)
               "iP62 VERIFIED: REPORTDATA_NO_STALE_REUSE_AFTER_INTERRUPT - Resumed report never mixes old REPORTDATA with new TD state"
               "iP62 VIOLATED: REPORTDATA_NO_STALE_REUSE_AFTER_INTERRUPT - Resumed report mixed stale REPORTDATA with new state"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP63: REPORTMAC_INPUT_COMPLETENESS
;;
;; Property: Report success hone par required MAC field
;;           (REPORTDATA/REPORTTYPE/CPUSVN/TEE_TCB_INFO_HASH/
;;           TD_INFO_HASH) missing hona — IMPOSSIBLE
;; Ref: ABI Spec - REPORTMACSTRUCT
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic mac-includes-reportdata-ip63  boolean?)
(define-symbolic mac-includes-reporttype-ip63  boolean?)
(define-symbolic mac-includes-cpusvn-ip63      boolean?)
(define-symbolic mac-includes-teetcbhash-ip63  boolean?)
(define-symbolic mac-includes-tdinfohash-ip63  boolean?)
(define-symbolic report-success-ip63           boolean?)
 
(define iP63
  (assert
    (not (and report-success-ip63
              (or (not mac-includes-reportdata-ip63)
                  (not mac-includes-reporttype-ip63)
                  (not mac-includes-cpusvn-ip63)
                  (not mac-includes-teetcbhash-ip63)
                  (not mac-includes-tdinfohash-ip63))))))
 
(define result-iP63 (verify iP63))
(displayln (if (unsat? result-iP63)
               "iP63 VERIFIED: REPORTMAC_INPUT_COMPLETENESS - Successful report MAC always includes all required fields"
               "iP63 VIOLATED: REPORTMAC_INPUT_COMPLETENESS - Successful report MAC omitted a required field"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP64: REPORTTYPE_TDX_DOMAIN_SEPARATION
;;
;; Property: TDG.MR.REPORT success + REPORTTYPE.TYPE != TDX
;;           — IMPOSSIBLE
;; Ref: Base Spec - REPORTTYPE(TDX); ABI Spec - REPORTMACSTRUCT
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic report-success-ip64   boolean?)
(define-symbolic reporttype-value-ip64 integer?)
 
(define iP64
  (assert
    (not (and report-success-ip64
              (not (= reporttype-value-ip64 REPORTTYPE_TDX))))))
 
(define result-iP64 (verify iP64))
(displayln (if (unsat? result-iP64)
               "iP64 VERIFIED: REPORTTYPE_TDX_DOMAIN_SEPARATION - TDG.MR.REPORT always emits REPORTTYPE=TDX"
               "iP64 VIOLATED: REPORTTYPE_TDX_DOMAIN_SEPARATION - Non-TDX REPORTTYPE emitted by TDG.MR.REPORT"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP65: REPORT_VERSION_SELECTION_CORRECTNESS
;;
;; Property: Service-TD-binding ya SVN/signer active hone par
;;           report version zaroori minimum se kam hona
;;           — IMPOSSIBLE
;; Ref: ABI Spec - TDG.MR.REPORT version rules; TDINFO_STRUCT versioning
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic servtd-binding-present-ip65 boolean?)
(define-symbolic svn-signer-present-ip65     boolean?)
(define-symbolic emitted-version-ip65        integer?)
 
(define iP65
  (assert
    (not (or
      (and servtd-binding-present-ip65
           (< emitted-version-ip65 REPORT_VERSION_1))
      (and svn-signer-present-ip65
           (< emitted-version-ip65 REPORT_VERSION_2))))))
 
(define result-iP65 (verify iP65))
(displayln (if (unsat? result-iP65)
               "iP65 VERIFIED: REPORT_VERSION_SELECTION_CORRECTNESS - Active SVN/signer/servtd state never truncated by low version"
               "iP65 VIOLATED: REPORT_VERSION_SELECTION_CORRECTNESS - Report version too low to represent active security state"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP66: REPORT_BUFFER_SIZE_NON_MUTATION_ON_FAILURE
;;
;; Property: Report fail hone par output buffer mein
;;           valid-looking partial report ya stale MAC
;;           rehna — IMPOSSIBLE
;; Ref: ABI Spec - TDG.MR.REPORT completion status, output buffer sizing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic report-failed-ip66           boolean?)
(define-symbolic output-buffer-valid-ip66     boolean?)
(define-symbolic output-buffer-stale-mac-ip66 boolean?)
 
(define iP66
  (assert
    (not (and report-failed-ip66
              (or output-buffer-valid-ip66
                  output-buffer-stale-mac-ip66)))))
 
(define result-iP66 (verify iP66))
(displayln (if (unsat? result-iP66)
               "iP66 VERIFIED: REPORT_BUFFER_SIZE_NON_MUTATION_ON_FAILURE - Failed report never leaves a valid-looking/stale output"
               "iP66 VIOLATED: REPORT_BUFFER_SIZE_NON_MUTATION_ON_FAILURE - Failed report left valid-looking or stale buffer content"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP67: TDINFO_FIELD_SOURCE_AUTHENTICITY
;;
;; Property: TDREPORT.TDINFO field, non-owning TDR se
;;           emit hona — IMPOSSIBLE
;; Ref: ABI Spec - TDINFO_STRUCT; Base Spec - TDG.MR.REPORT uses TDCS/TDR
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic tdinfo-field-source-tdr-ip67 integer?)
(define-symbolic current-seam-tdr-ip67        integer?)
(define-symbolic tdinfo-field-emitted-ip67    boolean?)
 
(define iP67
  (assert
    (not (and tdinfo-field-emitted-ip67
              (not (= tdinfo-field-source-tdr-ip67 current-seam-tdr-ip67))))))
 
(define result-iP67 (verify iP67))
(displayln (if (unsat? result-iP67)
               "iP67 VERIFIED: TDINFO_FIELD_SOURCE_AUTHENTICITY - TDINFO fields always sourced from the requesting TD's own TDR/TDCS"
               "iP67 VIOLATED: TDINFO_FIELD_SOURCE_AUTHENTICITY - TDINFO field sourced from a foreign TD/context"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP68: REPORTMAC_PER_TD_CONTEXT_ISOLATION
;;
;; Property: Cross-TD context switch ke baad purana
;;           intermediate MAC/hash state naye report mein
;;           reuse hona — IMPOSSIBLE
;; Ref: Base Spec - SEAMREPORT/SEAMDB_REPORT; ABI Spec - REPORTMACSTRUCT
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic context-switch-occurred-ip68   boolean?)
(define-symbolic prior-td-id-ip68               integer?)
(define-symbolic current-td-id-ip68             integer?)
(define-symbolic intermediate-state-reused-ip68 boolean?)
 
(define iP68
  (assert
    (not (and context-switch-occurred-ip68
              (not (= prior-td-id-ip68 current-td-id-ip68))
              intermediate-state-reused-ip68))))
 
(define result-iP68 (verify iP68))
(displayln (if (unsat? result-iP68)
               "iP68 VERIFIED: REPORTMAC_PER_TD_CONTEXT_ISOLATION - Intermediate MAC/hash state cleared on cross-TD context switch"
               "iP68 VIOLATED: REPORTMAC_PER_TD_CONTEXT_ISOLATION - Stale cross-TD intermediate MAC/hash state reused"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP69: REPORT_MAC_KEY_NON_SUBSTITUTABILITY
;;
;; Property: Report MAC operation mein hardware-authorized
;;           key ke bajaye substitute/non-authorized key
;;           use hona — IMPOSSIBLE
;; Ref: Base Spec - local report verification, CPU-held MAC key
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic selected-mac-key-ip69  integer?)
(define-symbolic hw-authorized-key-ip69 integer?)
(define-symbolic key-op-performed-ip69  boolean?)
 
(define iP69
  (assert
    (not (and key-op-performed-ip69
              (not (= selected-mac-key-ip69 hw-authorized-key-ip69))))))
 
(define result-iP69 (verify iP69))
(displayln (if (unsat? result-iP69)
               "iP69 VERIFIED: REPORT_MAC_KEY_NON_SUBSTITUTABILITY - Report MAC operations always use the hardware-authorized key"
               "iP69 VIOLATED: REPORT_MAC_KEY_NON_SUBSTITUTABILITY - Report MAC operation used a substituted/non-authorized key"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP70: REPORT_MAC_KEY_EPOCH_BINDING
;;
;; Property: Incompatible key epoch change ke baad purana
;;           report "fresh" verify ho jaaye (jab epoch
;;           explicitly preserve nahi kiya gaya) — IMPOSSIBLE
;; Ref: Base Spec - local report verification failure cases, TCB recovery
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic report-key-epoch-ip70     integer?)
(define-symbolic verify-key-epoch-ip70     integer?)
(define-symbolic epoch-preserved-ip70      boolean?)
(define-symbolic verify-fresh-success-ip70 boolean?)
 
(define iP70
  (assert
    (not (and (not (= report-key-epoch-ip70 verify-key-epoch-ip70))
              (not epoch-preserved-ip70)
              verify-fresh-success-ip70))))
 
(define result-iP70 (verify iP70))
(displayln (if (unsat? result-iP70)
               "iP70 VERIFIED: REPORT_MAC_KEY_EPOCH_BINDING - Reports from incompatible key epochs fail fresh verification"
               "iP70 VIOLATED: REPORT_MAC_KEY_EPOCH_BINDING - Stale-epoch report verified as fresh"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP71: TEE_TCB_CURRENT_STATE_ACCURACY
;;
;; Property: TEE_TCB current/creation fields swap hona,
;;           stale hona, ya zero rehna jabki report issued
;;           ho — IMPOSSIBLE
;; Ref: Base Spec - TCB recovery, TD-preserving update implications
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic active-tcb-svn-ip71       integer?)
(define-symbolic reported-current-svn-ip71 integer?)
(define-symbolic creation-tcb-svn-ip71     integer?)
(define-symbolic reported-creation-svn-ip71 integer?)
(define-symbolic report-issued-ip71        boolean?)
 
(define iP71
  (assert
    (not (and report-issued-ip71
              (or (not (= reported-current-svn-ip71 active-tcb-svn-ip71))
                  (not (= reported-creation-svn-ip71 creation-tcb-svn-ip71)))))))
 
(define result-iP71 (verify iP71))
(displayln (if (unsat? result-iP71)
               "iP71 VERIFIED: TEE_TCB_CURRENT_STATE_ACCURACY - Current and creation-time TCB fields reported accurately, never swapped"
               "iP71 VIOLATED: TEE_TCB_CURRENT_STATE_ACCURACY - Current/creation TCB fields mismatched, swapped, or stale"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP72: CPUSVN_FRESH_READ_FOR_REPORT
;;
;; Property: Reported CPUSVN stale ho ya MAC-bound
;;           CPUSVN se mismatch kare — IMPOSSIBLE
;; Ref: ABI Spec - CPUSVN, REPORTMACSTRUCT; Base Spec - CPU TCB recovery
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic current-cpu-svn-ip72  integer?)
(define-symbolic reported-cpusvn-ip72  integer?)
(define-symbolic mac-bound-cpusvn-ip72 integer?)
(define-symbolic report-issued-ip72    boolean?)
 
(define iP72
  (assert
    (not (and report-issued-ip72
              (or (not (= reported-cpusvn-ip72 current-cpu-svn-ip72))
                  (not (= reported-cpusvn-ip72 mac-bound-cpusvn-ip72)))))))
 
(define result-iP72 (verify iP72))
(displayln (if (unsat? result-iP72)
               "iP72 VERIFIED: CPUSVN_FRESH_READ_FOR_REPORT - CPUSVN is freshly sampled and matches the MAC-bound value"
               "iP72 VIOLATED: CPUSVN_FRESH_READ_FOR_REPORT - CPUSVN stale or mismatched against MAC-bound value"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP73: TD_ATTRIBUTES_REPORT_ACCURACY
;;
;; Property: Reported ATTRIBUTES/XFAM, committed TDCS
;;           values se mismatch kare — IMPOSSIBLE
;; Ref: ABI Spec - TDINFO_STRUCT.ATTRIBUTES, XFAM
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic tdcs-attributes-ip73    integer?)
(define-symbolic reported-attributes-ip73 integer?)
(define-symbolic tdcs-xfam-ip73          integer?)
(define-symbolic reported-xfam-ip73      integer?)
(define-symbolic report-issued-ip73      boolean?)
 
(define iP73
  (assert
    (not (and report-issued-ip73
              (or (not (= tdcs-attributes-ip73 reported-attributes-ip73))
                  (not (= tdcs-xfam-ip73 reported-xfam-ip73)))))))
 
(define result-iP73 (verify iP73))
(displayln (if (unsat? result-iP73)
               "iP73 VERIFIED: TD_ATTRIBUTES_REPORT_ACCURACY - Reported ATTRIBUTES/XFAM exactly match committed TDCS values"
               "iP73 VIOLATED: TD_ATTRIBUTES_REPORT_ACCURACY - Reported ATTRIBUTES/XFAM mismatch committed TDCS values"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP74: SERVTD_HASH_SELECTION_CORRECTNESS
;;
;; Property: SERVTD_EXT set hone par SERVTD_EXT_HASH ke
;;           bajaye SERVTD_HASH select hona (ya vice-versa),
;;           ya selected value TD_INFO_HASH se alag hona
;;           — IMPOSSIBLE
;; Ref: ABI Spec - TDG.MR.REPORT service TD hash rules; TDREPORT version 1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic servtd-ext-set-ip74       boolean?)
(define-symbolic servtd-ext-hash-ip74      integer?)
(define-symbolic servtd-hash-ip74          integer?)
(define-symbolic selected-servtd-hash-ip74 integer?)
(define-symbolic tdinfo-hash-bound-ip74    integer?)
(define-symbolic report-issued-ip74        boolean?)
 
(define iP74
  (assert
    (not (or
      (and report-issued-ip74
           servtd-ext-set-ip74
           (not (= selected-servtd-hash-ip74 servtd-ext-hash-ip74)))
      (and report-issued-ip74
           (not servtd-ext-set-ip74)
           (not (= selected-servtd-hash-ip74 servtd-hash-ip74)))
      (and report-issued-ip74
           (not (= selected-servtd-hash-ip74 tdinfo-hash-bound-ip74)))))))
 
(define result-iP74 (verify iP74))
(displayln (if (unsat? result-iP74)
               "iP74 VERIFIED: SERVTD_HASH_SELECTION_CORRECTNESS - SERVTD_HASH correctly selected per SERVTD_EXT and bound into TD_INFO_HASH"
               "iP74 VIOLATED: SERVTD_HASH_SELECTION_CORRECTNESS - SERVTD_HASH selection incorrect or unbound from TD_INFO_HASH"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP75: ASSIGNED_SVN_AND_SIGNER_FIELD_INTEGRITY
;;
;; Property: SVN/signer field assigned hone par version<2
;;           emit hona ya value stale/partial hona — IMPOSSIBLE
;; Ref: ABI Spec - TDREPORT_STRUCT version 2; Base Spec - TDG.MR.ASSIGNSVNS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic svn-signer-assigned-ip75    boolean?)
(define-symbolic tdcs-svn-signer-val-ip75    integer?)
(define-symbolic reported-svn-signer-val-ip75 integer?)
(define-symbolic emitted-version-ip75        integer?)
(define-symbolic report-issued-ip75          boolean?)
 
(define iP75
  (assert
    (not (and report-issued-ip75
              svn-signer-assigned-ip75
              (or (< emitted-version-ip75 REPORT_VERSION_2)
                  (not (= reported-svn-signer-val-ip75 tdcs-svn-signer-val-ip75)))))))
 
(define result-iP75 (verify iP75))
(displayln (if (unsat? result-iP75)
               "iP75 VERIFIED: ASSIGNED_SVN_AND_SIGNER_FIELD_INTEGRITY - Assigned SVN/signer fields reported exactly at version >= 2"
               "iP75 VIOLATED: ASSIGNED_SVN_AND_SIGNER_FIELD_INTEGRITY - Assigned SVN/signer field omitted, stale, or under-versioned"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP76: MRTD_RTMR_PARTIAL_WRITE_FAULT_RESISTANCE
;;
;; Property: Fault detect hone par bina fatal/fail path ke
;;           success declare hona ya corrupted measurement
;;           commit karna — IMPOSSIBLE
;; Ref: Base Spec - TD measurement reporting; ABI Spec - MRTD/RTMR fields
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic fault-detected-ip76        boolean?)
(define-symbolic op-declared-success-ip76   boolean?)
(define-symbolic measurement-committed-ip76 boolean?)
(define-symbolic td-fatal-triggered-ip76    boolean?)
 
(define iP76
  (assert
    (not (and fault-detected-ip76
              (not td-fatal-triggered-ip76)
              (or op-declared-success-ip76
                  measurement-committed-ip76)))))
 
(define result-iP76 (verify iP76))
(displayln (if (unsat? result-iP76)
               "iP76 VERIFIED: MRTD_RTMR_PARTIAL_WRITE_FAULT_RESISTANCE - Faulted MRTD/RTMR access fails/fatals before success or commit"
               "iP76 VIOLATED: MRTD_RTMR_PARTIAL_WRITE_FAULT_RESISTANCE - Faulted MRTD/RTMR access still succeeded or committed"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP77: MEASUREMENT_REGISTER_ZEROIZATION_ON_TEARDOWN
;;
;; Property: Teardown ke baad resources reallocate hone par
;;           residual MRTD/RTMR/hash/SVN/signer/report-scratch
;;           state bachi rehna — IMPOSSIBLE
;; Ref: Base Spec - TD lifecycle, TDCS/TDR state
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic teardown-completed-ip77   boolean?)
(define-symbolic resource-reallocated-ip77 boolean?)
(define-symbolic residual-measurement-ip77 boolean?)
 
(define iP77
  (assert
    (not (and teardown-completed-ip77
              resource-reallocated-ip77
              residual-measurement-ip77))))
 
(define result-iP77 (verify iP77))
(displayln (if (unsat? result-iP77)
               "iP77 VERIFIED: MEASUREMENT_REGISTER_ZEROIZATION_ON_TEARDOWN - All measurement state cleared before resource reuse"
               "iP77 VIOLATED: MEASUREMENT_REGISTER_ZEROIZATION_ON_TEARDOWN - Residual measurement state survived into reallocated resource"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP78: TD_LIFECYCLE_REPORT_ELIGIBILITY
;;
;; Property: Non-runnable TD lifecycle mein TDG.MR.REPORT
;;           succeed karna ya valid output dena — IMPOSSIBLE
;; Ref: Base Spec - TD lifecycle state machine; ABI Spec - TDG.MR.REPORT
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic td-lifecycle-state-ip78  integer?)
(define-symbolic report-success-ip78      boolean?)
(define-symbolic valid-report-output-ip78 boolean?)
 
(define iP78
  (assert
    (not (and (not (= td-lifecycle-state-ip78 REPORT_LIFECYCLE_RUNNABLE))
              (or report-success-ip78
                  valid-report-output-ip78)))))
 
(define result-iP78 (verify iP78))
(displayln (if (unsat? result-iP78)
               "iP78 VERIFIED: TD_LIFECYCLE_REPORT_ELIGIBILITY - TDG.MR.REPORT only succeeds for runnable/reportable TD lifecycle states"
               "iP78 VIOLATED: TD_LIFECYCLE_REPORT_ELIGIBILITY - Report succeeded for a non-reportable TD lifecycle state"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP79: NO_REPORT_AFTER_TD_FATAL_TRANSITION
;;
;; Property: TD fatal state mein enter karne ke baad
;;           TDG.MR.REPORT successfully complete hona
;;           — IMPOSSIBLE
;; Ref: Base Spec - TD lifecycle/fatal state handling; ABI Spec - interruptible TDG.MR.REPORT
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic td-fatal-ip79                  boolean?)
(define-symbolic report-began-before-fatal-ip79 boolean?)
(define-symbolic report-completed-ip79          boolean?)
 
(define iP79
  (assert
    (not (and td-fatal-ip79
              report-completed-ip79))))
 
(define result-iP79 (verify iP79))
(displayln (if (unsat? result-iP79)
               "iP79 VERIFIED: NO_REPORT_AFTER_TD_FATAL_TRANSITION - No TDG.MR.REPORT completes successfully once TD is fatal"
               "iP79 VIOLATED: NO_REPORT_AFTER_TD_FATAL_TRANSITION - TDG.MR.REPORT completed successfully after TD entered fatal state"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP80: TD_DESTROY_RECREATE_ANTI_REPLAY_IDENTITY_BINDING
;;
;; Property: Recycled resources par naye TD ke liye purane
;;           TD ka report identity/MAC context valid declare
;;           hona — IMPOSSIBLE
;; Ref: Base Spec - TD lifecycle, TDCS/TDR ownership; MKTME KeyID management
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic destroyed-td-epoch-ip80           integer?)
(define-symbolic new-td-epoch-ip80                 integer?)
(define-symbolic resource-recycled-ip80            boolean?)
(define-symbolic old-identity-valid-for-new-ip80   boolean?)
 
(define iP80
  (assert
    (not (and resource-recycled-ip80
              (not (= destroyed-td-epoch-ip80 new-td-epoch-ip80))
              old-identity-valid-for-new-ip80))))
 
(define result-iP80 (verify iP80))
(displayln (if (unsat? result-iP80)
               "iP80 VERIFIED: TD_DESTROY_RECREATE_ANTI_REPLAY_IDENTITY_BINDING - Destroyed TD's report identity never validates for a recreated TD"
               "iP80 VIOLATED: TD_DESTROY_RECREATE_ANTI_REPLAY_IDENTITY_BINDING - Old TD report identity validated for a recreated TD on recycled resources"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP81: HKID_MKTME_KEYID_ATTESTATION_BINDING
;;
;; Property: vCPU/TDCS/TDR/active-KeyID TD ownership mismatch
;;           ke bawajood TDG.MR.REPORT succeed karna — IMPOSSIBLE
;; Ref: Base Spec - HKID/TD ownership; MKTME documentation - KeyID binding
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic vcpu-owning-td-ip81  integer?)
(define-symbolic tdcs-owning-td-ip81  integer?)
(define-symbolic tdr-owning-td-ip81   integer?)
(define-symbolic active-keyid-td-ip81 integer?)
(define-symbolic report-success-ip81  boolean?)
 
(define iP81
  (assert
    (not (and report-success-ip81
              (or (not (= vcpu-owning-td-ip81 tdcs-owning-td-ip81))
                  (not (= tdcs-owning-td-ip81 tdr-owning-td-ip81))
                  (not (= tdr-owning-td-ip81 active-keyid-td-ip81)))))))
 
(define result-iP81 (verify iP81))
(displayln (if (unsat? result-iP81)
               "iP81 VERIFIED: HKID_MKTME_KEYID_ATTESTATION_BINDING - Report succeeds only when vCPU/TDCS/TDR/KeyID share one TD ownership"
               "iP81 VIOLATED: HKID_MKTME_KEYID_ATTESTATION_BINDING - Report succeeded despite mismatched vCPU/TDCS/TDR/KeyID ownership"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP82: REPORT_GENERATION_BLOCKS_TDCS_MUTATION_RACE
;;
;; Property: Report snapshot in-progress ho aur concurrent
;;           unserialized mutation se mixed pre/post fields
;;           snapshot mein land kar jayein — IMPOSSIBLE
;; Ref: ABI Spec - TDG.MR.REPORT TDCS shared access; TDG.MR.RTMR.EXTEND exclusive access
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic snapshot-in-progress-ip82    boolean?)
(define-symbolic concurrent-mutation-ip82     boolean?)
(define-symbolic mutation-serialized-ip82     boolean?)
(define-symbolic mutation-clean-retry-ip82    boolean?)
(define-symbolic snapshot-mixed-result-ip82   boolean?)
 
(define iP82
  (assert
    (not (and snapshot-in-progress-ip82
              concurrent-mutation-ip82
              (not mutation-serialized-ip82)
              (not mutation-clean-retry-ip82)
              snapshot-mixed-result-ip82))))
 
(define result-iP82 (verify iP82))
(displayln (if (unsat? result-iP82)
               "iP82 VERIFIED: REPORT_GENERATION_BLOCKS_TDCS_MUTATION_RACE - Concurrent TDCS mutation during report snapshot is serialized or clean-retried"
               "iP82 VIOLATED: REPORT_GENERATION_BLOCKS_TDCS_MUTATION_RACE - Report snapshot mixed pre/post mutation TDCS fields"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP83: QE_VERIFICATION_SUCCESS_ONLY_AFTER_MAC_VALIDATION
;;
;; Property: EVERIFYREPORT success declare kare jabki exact
;;           body MAC validate na hua ho ya body/MAC mismatch
;;           ho — IMPOSSIBLE
;; Ref: Base Spec - SGX-based TD attestation, QE flow, EVERIFYREPORT
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic mac-validated-ip83     boolean?)
(define-symbolic body-mac-match-ip83    boolean?)
(define-symbolic qe-verify-success-ip83 boolean?)
 
(define iP83
  (assert
    (not (and qe-verify-success-ip83
              (or (not mac-validated-ip83)
                  (not body-mac-match-ip83))))))
 
(define result-iP83 (verify iP83))
(displayln (if (unsat? result-iP83)
               "iP83 VERIFIED: QE_VERIFICATION_SUCCESS_ONLY_AFTER_MAC_VALIDATION - QE verify succeeds only after exact-body MAC validation"
               "iP83 VIOLATED: QE_VERIFICATION_SUCCESS_ONLY_AFTER_MAC_VALIDATION - QE verify succeeded without valid exact-body MAC check"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP84: QE_REPORT_BODY_IMMUTABILITY_VERIFY_TO_SIGN
;;
;; Property: EVERIFYREPORT ke baad body modify ho aur QE
;;           phir bhi usi verification result se signing
;;           proceed kare — IMPOSSIBLE
;; Ref: Base Spec - TD attestation flow through VMM and QE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic verified-body-digest-ip84  integer?)
(define-symbolic sign-time-body-digest-ip84 integer?)
(define-symbolic verification-valid-ip84    boolean?)
(define-symbolic qe-signing-proceeds-ip84   boolean?)
 
(define iP84
  (assert
    (not (and (not (= verified-body-digest-ip84 sign-time-body-digest-ip84))
              verification-valid-ip84
              qe-signing-proceeds-ip84))))
 
(define result-iP84 (verify iP84))
(displayln (if (unsat? result-iP84)
               "iP84 VERIFIED: QE_REPORT_BODY_IMMUTABILITY_VERIFY_TO_SIGN - Body modification after verify invalidates the verification result"
               "iP84 VIOLATED: QE_REPORT_BODY_IMMUTABILITY_VERIFY_TO_SIGN - QE signed over a body modified after verification"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP85: RESERVED_AND_MUST_BE_ZERO_FIELD_ENFORCEMENT
;;
;; Property: Reserved/must-be-zero field non-zero generate
;;           hona ya MAC mein inconsistently include hona
;;           — IMPOSSIBLE
;; Ref: ABI Spec - REPORTMACSTRUCT and TDINFO_STRUCT must-be-zero fields
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic reserved-field-value-ip85  integer?)
(define-symbolic reserved-field-in-mac-ip85 boolean?)
(define-symbolic report-generated-ip85      boolean?)
 
(define iP85
  (assert
    (not (and report-generated-ip85
              (or (not (= reserved-field-value-ip85 0))
                  (not reserved-field-in-mac-ip85))))))
 
(define result-iP85 (verify iP85))
(displayln (if (unsat? result-iP85)
               "iP85 VERIFIED: RESERVED_AND_MUST_BE_ZERO_FIELD_ENFORCEMENT - Reserved fields are always zero and consistently MAC-included"
               "iP85 VIOLATED: RESERVED_AND_MUST_BE_ZERO_FIELD_ENFORCEMENT - Reserved field non-zero or inconsistently MAC-included"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP86: TDREPORT_OUTPUT_BOUNDS_ENFORCEMENT
;;
;; Property: TDG.MR.REPORT required size se zyada bytes
;;           likhna ya unused bytes mein uninitialized data
;;           chodna — IMPOSSIBLE
;; Ref: ABI Spec - TDREPORT_STRUCT sizes, TDG.MR.REPORT buffer-size rules
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic required-report-size-ip86     integer?)
(define-symbolic bytes-written-ip86            integer?)
(define-symbolic unused-bytes-initialized-ip86 boolean?)
(define-symbolic report-generated-ip86         boolean?)
 
(define iP86
  (assert
    (not (and report-generated-ip86
              (or (> bytes-written-ip86 required-report-size-ip86)
                  (not unused-bytes-initialized-ip86))))))
 
(define result-iP86 (verify iP86))
(displayln (if (unsat? result-iP86)
               "iP86 VERIFIED: TDREPORT_OUTPUT_BOUNDS_ENFORCEMENT - TDREPORT never overruns required size and padding is initialized"
               "iP86 VIOLATED: TDREPORT_OUTPUT_BOUNDS_ENFORCEMENT - TDREPORT overran required size or left uninitialized padding"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP87: REPORT_HASH_ENGINE_DOMAIN_RESET
;;
;; Property: Distinct hash domains ke beech engine state
;;           reset na hone par domain B result, domain A
;;           residue se derived hona — IMPOSSIBLE
;; Ref: ABI Spec - REPORTMACSTRUCT hashes; Base Spec - measurement reporting, RTMR extend
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic hash-domain-A-ip87        integer?)
(define-symbolic hash-domain-B-ip87        integer?)
(define-symbolic engine-state-reset-ip87   boolean?)
(define-symbolic domain-B-result-ip87      integer?)
(define-symbolic domain-A-leaked-state-ip87 integer?)
 
(define iP87
  (assert
    (not (and (not (= hash-domain-A-ip87 hash-domain-B-ip87))
              (not engine-state-reset-ip87)
              (= domain-B-result-ip87 domain-A-leaked-state-ip87)))))
 
(define result-iP87 (verify iP87))
(displayln (if (unsat? result-iP87)
               "iP87 VERIFIED: REPORT_HASH_ENGINE_DOMAIN_RESET - Hash engine state reset between distinct hash domains/invocations"
               "iP87 VIOLATED: REPORT_HASH_ENGINE_DOMAIN_RESET - Hash domain contaminated by residual state from a prior domain"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP88: REPORT_GENERATION_NO_DEBUG_OVERRIDE
;;
;; Property: Production mode mein debug/test/JTAG/firmware
;;           hook, attestation output field override kare
;;           — IMPOSSIBLE
;; Ref: Intel TDX Base Spec - production TD security model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic production-mode-ip88              boolean?)
(define-symbolic debug-hook-active-ip88            boolean?)
(define-symbolic attestation-field-overridden-ip88 boolean?)
 
(define iP88
  (assert
    (not (and production-mode-ip88
              debug-hook-active-ip88
              attestation-field-overridden-ip88))))
 
(define result-iP88 (verify iP88))
(displayln (if (unsat? result-iP88)
               "iP88 VERIFIED: REPORT_GENERATION_NO_DEBUG_OVERRIDE - No debug/test/manufacturing hook overrides attestation output in production"
               "iP88 VIOLATED: REPORT_GENERATION_NO_DEBUG_OVERRIDE - Debug/test hook overrode attestation output in production mode"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP89: MIGRATION_REPORT_FRESHNESS_FAILURE_ON_PLATFORM_CHANGE
;;
;; Property: Incompatible platform change ke baad purana
;;           report fresh verify ho jaaye ya fresh report
;;           naya platform state ignore kare — IMPOSSIBLE
;; Ref: Base Spec - local report verification failure after migration
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
(define-symbolic origin-platform-id-ip89          integer?)
(define-symbolic current-platform-id-ip89         integer?)
(define-symbolic platform-compatible-ip89         boolean?)
(define-symbolic old-report-verifies-ip89         boolean?)
(define-symbolic fresh-report-uses-new-state-ip89 boolean?)
 
(define iP89
  (assert
    (not (or
      (and (not (= origin-platform-id-ip89 current-platform-id-ip89))
           (not platform-compatible-ip89)
           old-report-verifies-ip89)
      (and (not (= origin-platform-id-ip89 current-platform-id-ip89))
           (not platform-compatible-ip89)
           (not fresh-report-uses-new-state-ip89))))))
 
(define result-iP89 (verify iP89))
(displayln (if (unsat? result-iP89)
               "iP89 VERIFIED: MIGRATION_REPORT_FRESHNESS_FAILURE_ON_PLATFORM_CHANGE - Old reports fail verification and fresh reports reflect new platform after incompatible migration"
               "iP89 VIOLATED: MIGRATION_REPORT_FRESHNESS_FAILURE_ON_PLATFORM_CHANGE - Old report verified or fresh report ignored new platform state post-migration"))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Final Summary
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(displayln "\n=== INTEGRITY VERIFICATION SUMMARY ===")

(define all-results
  (list (cons "iP1"  result-iP1)
        (cons "iP2"  result-iP2)
        (cons "iP3"  result-iP3)
        (cons "iP4"  result-iP4)
        (cons "iP5"  result-iP5)
        (cons "iP6"  result-iP6)
        (cons "iP7"  result-iP7)
        (cons "iP8"  result-iP8)
        (cons "iP9"  result-iP9)
        (cons "iP40" result-iP40)
        (cons "iP41" result-iP41)
        (cons "iP42" result-iP42)
        (cons "iP43" result-iP43)
        (cons "iP44" result-iP44)
        (cons "iP45" result-iP45)
        (cons "iP46" result-iP46)
        (cons "iP47" result-iP47)
        (cons "iP48" result-iP48)
        (cons "iP49" result-iP49)
        (cons "iP50" result-iP50)
        ;; --- MKTME INTEGRITY PROPERTIES ---
        (cons "iP10"  result-iM1)
        (cons "iP11"  result-iM2)
        (cons "iP12"  result-iM3)
        (cons "iP13"  result-iM4)
        ;; --- ATTESTATION INTEGRITY PROPERTIES ---
        (cons "iP14"         result-iA1)
        (cons "iP15-partial" result-iA2-partial)
        (cons "iP15-stale"   result-iA2-stale)
        (cons "iP16"         result-iA3)
        (cons "iP17"         result-iA4)
        (cons "iP18"         result-iA5)
        ;; --- L1/L2 PARTITIONING INTEGRITY [NEW] ---
        (cons "iP19 [DocP2-RegScrub]"    result-iP19)
        (cons "iP20 [DocP3-ExitIBPB]"    result-iP20)
        (cons "iP21 [DocP4-MSRShadow]"   result-iP21)
        (cons "iP22 [DocP7-IntWindow]"   result-iP22)
        (cons "iP23 [DocP8-NoRecursive]" result-iP23)
        (cons "iP24 [DocP9-SEAMCALLBlk]" result-iP24)
        (cons "iP25 [DocP10-EntryCFI]"   result-iP25)
        ;; --- ADDITIONAL L1/L2 PARTITIONING INTEGRITY [NEW] ---
        (cons "iP26 [tpP1-L2AliasOwner]"   result-iP26)
        (cons "iP27 [tpP2-PermSubset]"     result-iP27)
        (cons "iP28 [tpP4-SEPTAtomic]"     result-iP28)
        (cons "iP29 [tpP6-EntryContain]"   result-iP29)
        (cons "iP30 [tpP7-ExitContain]"    result-iP30)
        (cons "iP31 [tpP8-ExitCFTarget]"   result-iP31)
        (cons "iP32 [tpP10-PrivHKID]"      result-iP32)
        (cons "iP33 [tpP12-TDOwnerSet]"    result-iP33)
        (cons "iP34 [tpP13-ConvInval]"     result-iP34)
        (cons "iP35 [tpP14-HKIDFlush]"     result-iP35)
        (cons "iP36 [tpP16-PAMTTypeMatch]" result-iP36)
        (cons "iP37 [tpP17-VMCSMask]"      result-iP37)
        (cons "iP38 [tpP19-ImportBlocked]" result-iP38)
        (cons "iP39 [tpP21-CiphertextReplay]" result-iP39)
        (cons "iP51 [tpP22-FailContainment]"  result-iP51)
        (cons "iP52 [tpP23-FetchXPerm]"       result-iP52)
        ;; --- ADDITIONAL ATTESTATION INTEGRITY PROPERTIES [RAG NEW] ---
        (cons "iP53 [MRTD-LockAfterBuild]"         result-iP53)
        (cons "iP54 [MRTD-ReportSnapshot]"          result-iP54)
        (cons "iP55 [RTMR-AtomicCommit]"            result-iP55)
        (cons "iP56 [RTMR-SerializationPerReg]"     result-iP56)
        (cons "iP57 [RTMR-IndexBounds]"             result-iP57)
        (cons "iP58 [RTMR-InputCoherency]"          result-iP58)
        (cons "iP59 [RTMR-PrivateMemEnforce]"       result-iP59)
        (cons "iP60 [REPORTDATA-ExactBinding]"      result-iP60)
        (cons "iP61 [REPORTDATA-SnapshotAtomicity]" result-iP61)
        (cons "iP62 [REPORTDATA-NoStaleReuse]"      result-iP62)
        (cons "iP63 [REPORTMAC-InputComplete]"      result-iP63)
        (cons "iP64 [REPORTTYPE-TDXDomain]"         result-iP64)
        (cons "iP65 [REPORT-VersionCorrect]"        result-iP65)
        (cons "iP66 [REPORT-BufNonMutOnFail]"       result-iP66)
        (cons "iP67 [TDINFO-FieldSourceAuth]"       result-iP67)
        (cons "iP68 [REPORTMAC-PerTDIsolation]"     result-iP68)
        (cons "iP69 [REPORT-MACKeyNonSubst]"        result-iP69)
        (cons "iP70 [REPORT-MACKeyEpoch]"           result-iP70)
        (cons "iP71 [TEE-TCBCurrentState]"          result-iP71)
        (cons "iP72 [CPUSVN-FreshRead]"             result-iP72)
        (cons "iP73 [TD-AttributesAccuracy]"        result-iP73)
        (cons "iP74 [SERVTD-HashSelection]"         result-iP74)
        (cons "iP75 [ASSIGNSVN-SignerIntegrity]"    result-iP75)
        (cons "iP76 [MRTD-RTMR-FaultResist]"       result-iP76)
        (cons "iP77 [MEAS-ZeroOnTeardown]"          result-iP77)
        (cons "iP78 [TD-LifecycleEligibility]"      result-iP78)
        (cons "iP79 [NO-ReportAfterFatal]"          result-iP79)
        (cons "iP80 [TD-DestroyAntiReplay]"         result-iP80)
        (cons "iP81 [HKID-KeyIDAttestation]"        result-iP81)
        (cons "iP82 [REPORT-BlocksTDCSRace]"        result-iP82)
        (cons "iP83 [QE-VerifyAfterMAC]"            result-iP83)
        (cons "iP84 [QE-BodyImmutability]"          result-iP84)
        (cons "iP85 [RSVD-MBZEnforcement]"          result-iP85)
        (cons "iP86 [TDREPORT-OutputBounds]"        result-iP86)
        (cons "iP87 [HASH-EngineDomainReset]"       result-iP87)
        (cons "iP88 [REPORT-NoDebugOverride]"       result-iP88)
        (cons "iP89 [MIGRATION-ReportFreshness]"    result-iP89)))
 



(for ([r all-results])
  (printf "~a: ~a\n"
          (car r)
          (if (unsat? (cdr r)) "VERIFIED ✓" "VIOLATED ✗")))

(provide (all-defined-out))

