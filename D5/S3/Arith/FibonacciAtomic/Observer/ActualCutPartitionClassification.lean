/- GID: D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionClassification
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: All-source sparse literal row recovery is exactly common-suffix recutting. -/

import D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder
import D5.S3.ConceptDynamics.RefinementFactorization.RealizedImageKernelFactorization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionClassification

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address)
open D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder
open D5.S3.ConceptDynamics.RefinementFactorization.RealizedImageKernelFactorization

private theorem recovery_has_suffix (P Q : CutSet) (hP : CutPrefixFree P) (hQ : CutPrefixFree Q)
    (recover : Recovers P Q) : HasCommonSuffix P Q := by
  have cover := recovery_covers P Q hP recover
  by_cases qe : Q = ∅
  · have pe : P = ∅ := by
      ext p
      constructor
      · intro hp
        obtain ⟨q, hq, _⟩ := cover p hp
        simp [qe] at hq
      · simp
    rw [qe, commonSuffix_empty_right]
    exact pe
  · obtain ⟨q0, hq0⟩ := Finset.nonempty_iff_ne_empty.mpr qe
    have uniform (q : Address) (hq : q ∈ Q) (s : Address) :
        q ++ s ∈ P ↔ q0 ++ s ∈ P := by
      constructor
      · intro hp
        by_contra absent
        obtain ⟨u, v, old, new⟩ := nonuniform_failure_pair P Q hP hQ cover q q0 s hq hq0 hp absent
        exact new (recover u v old)
      · intro hp
        by_contra absent
        obtain ⟨u, v, old, new⟩ := nonuniform_failure_pair P Q hP hQ cover q0 q s hq0 hq hp absent
        exact new (recover u v old)
    refine ⟨cutSection P q0, cutSection_prefixFree P hP q0, ?_⟩
    intro p
    constructor
    · intro hp
      obtain ⟨q, hq, pre⟩ := cover p hp
      obtain ⟨s, eq⟩ := pre
      refine ⟨q, hq, s, ?_, eq.symm⟩
      apply (mem_cutSection_iff P q0 s).mpr
      exact ⟨(uniform q hq s).mp (by simpa [eq] using hp), List.prefix_append _ _⟩
    · rintro ⟨q, hq, s, hs, rfl⟩
      exact (uniform q hq s).mpr (cutSection_mem_append P q0 s hs)

private theorem empty_prefixFree : CutPrefixFree (∅ : CutSet) := by
  intro p hp
  simp at hp

private theorem root_prefixFree : CutPrefixFree ({[]} : CutSet) := by
  intro p hp q hq _
  have ep : p = [] := by simpa using hp
  have eq : q = [] := by simpa using hq
  exact ep.trans eq.symm

private theorem empty_old_recovers (Q : CutSet) (hQ : CutPrefixFree Q) : Recovers ∅ Q := by
  apply commonSuffix_recovers ∅ Q empty_prefixFree hQ
  exact ⟨∅, empty_prefixFree, by intro p; simp⟩

private theorem empty_new_boundary (P : CutSet) (hP : CutPrefixFree P) : Recovers P ∅ ↔ P = ∅ := by
  constructor
  · intro h
    exact (commonSuffix_empty_right P).mp (recovery_has_suffix P ∅ hP empty_prefixFree h)
  · rintro rfl
    exact empty_old_recovers ∅ empty_prefixFree

private theorem root_new_recovers (P : CutSet) (hP : CutPrefixFree P) : Recovers P {[]} :=
  commonSuffix_recovers P {[]} hP root_prefixFree (commonSuffix_root_right P hP)

private theorem root_old_boundary (Q : CutSet) (hQ : CutPrefixFree Q) :
    Recovers {[]} Q ↔ Q = {[]} := by
  constructor
  · intro recover
    obtain ⟨q, hq, pre⟩ := recovery_covers {[]} Q root_prefixFree recover [] (by simp)
    have nil : q = [] := List.prefix_nil.mp pre
    subst q
    have eq := D5.S0.Computability.Coding.PrefixFreeCode.isPrefixFree_eq_singleton_nil hQ hq
    apply Finset.coe_injective
    simpa using eq
  · rintro rfl
    exact root_new_recovers {[]} root_prefixFree

/-- Full all-source Theorem 64.2, its executable finite comparison and decoder,
unique nonempty suffix, and every empty/root boundary. -/
theorem result (P Q : CutSet) (hP : CutPrefixFree P) (hQ : CutPrefixFree Q) :
    ((∃! factor : Set.range (canonicalRow P) → Set.range (canonicalRow Q),
      Set.rangeFactorization (canonicalRow Q) = factor ∘ Set.rangeFactorization (canonicalRow P)) ↔
      HasCommonSuffix P Q) ∧
    (HasCommonSuffix P Q → ∀ u : Source, rowDecoder Q (canonicalRow P u) = canonicalRow Q u) ∧
    (commonSuffixTest P Q = true ↔ HasCommonSuffix P Q) ∧
    (Q.Nonempty → ∀ S T : CutSet,
      (∀ p, p ∈ P ↔ ∃ q ∈ Q, ∃ s ∈ S, p = q ++ s) →
      (∀ p, p ∈ P ↔ ∃ q ∈ Q, ∃ t ∈ T, p = q ++ t) → S = T) ∧
    Recovers ∅ Q ∧ (Recovers P ∅ ↔ P = ∅) ∧
    Recovers P {[]} ∧ (Recovers {[]} Q ↔ Q = {[]}) ∧
    (∀ (u : Source) (p : Address), p ∈ P → subtree p u = none →
      ∃ a : Address, ∃ b : Bool, a.IsPrefix p ∧ a ≠ p ∧
        rowAt a (canonicalRow P u) = some (.of (.inl b))) ∧
    (∀ u v : Source,
      canonicalRow P u = canonicalRow P v ↔ literalRecord P u = literalRecord P v) := by
  refine ⟨?_, ?_, commonSuffixTest_correct P Q hP hQ, ?_,
    empty_old_recovers Q hQ, empty_new_boundary P hP,
    root_new_recovers P hP, root_old_boundary Q hQ,
    (fun u p hp hm => canonicalRow_absent_guard P hP u p hp hm),
    canonicalRow_record_iff P hP⟩
  · refine (realized_image_unique_factorization_iff_reverse_kernel
      (canonicalRow Q) (canonicalRow P)).trans ?_
    change Recovers P Q ↔ HasCommonSuffix P Q
    exact ⟨recovery_has_suffix P Q hP hQ, commonSuffix_recovers P Q hP hQ⟩
  · rintro ⟨S, _, prod⟩ u
    exact commonSuffix_decoder_correct P Q S hP hQ prod u
  · intro nonempty S T ps pt
    exact commonSuffix_unique P Q S T hQ nonempty ps pt

#print axioms result

end D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionClassification
