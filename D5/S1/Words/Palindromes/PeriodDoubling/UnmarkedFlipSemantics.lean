/- GID: D5/S1/Words/Palindromes/PeriodDoubling/UnmarkedFlipSemantics
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/UnmarkedFlipSemantics
   mirror-E: none(waiver:literal-unmarked-negation-flag)
   anchors: []
   utility: none
   digest: The unmarked flip flag records exact pointwise negation of the lower signed streams. -/

/-
proof_shape: content (unmarked_path_flip_semantics)
escape_witness: Backward mode rigidity and path induction identify the persistent negation flag.
admission_basis: escape-witness
Direct frozen dependencies: none; PrefixPathRealization and BaseSignedStreams are delivered here.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.PrefixPathRealization
import D5.S1.Words.Palindromes.PeriodDoubling.BaseSignedStreams
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace D5.S1.Words.Palindromes.PeriodDoubling
open MarkedPrefixCertificates BaseCertificates

/-- Before marker selection, the flip flag means that every output digit negates its input. -/
theorem unmarked_path_flip_semantics {s t : List ℤ} {xs : List (ℤ × ℤ × ℤ × ℤ)}
    (p : prefixRawAutomaton.Path s t xs) (ht : t[1]?.getD 0=0) :
    (t[2]?.getD 0 ≠ 0 ↔ s[2]?.getD 0 ≠ 0 ∧
      ∀ z ∈ (pathOutputs (fun _ _ (q : List ℤ) => (baseTable (q[0]?.getD 0).toNat).1[10]?.getD 0) p).zip
        (pathOutputs (fun _ _ (q : List ℤ) => (baseTable (q[0]?.getD 0).toNat).1[12]?.getD 0) p),
        z.1+z.2=0) := by
  have back {s q : List ℤ} {a : ℤ × ℤ × ℤ × ℤ}
      (he : (q,a) ∈ successors s) (hq : q[1]?.getD 0=0) :
      s[1]?.getD 0=0 ∧ (q[2]?.getD 0≠0 ↔ s[2]?.getD 0≠0 ∧
        (baseTable (q[0]?.getD 0).toNat).1[10]?.getD 0+
          (baseTable (q[0]?.getD 0).toNat).1[12]?.getD 0=0) := by
    obtain ⟨e,he,hmem⟩ := List.mem_flatMap.mp he
    unfold nextMarker at hmem
    dsimp only at hmem
    split at hmem
    · simp at hmem
    · split at hmem
      · rename_i hs
        split at hmem
        · simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl,ha⟩ | ⟨rfl,ha⟩
          · refine ⟨hs,?_⟩
            simp
          · norm_num at hq
        · simp only [List.mem_singleton,Prod.mk.injEq] at hmem
          obtain ⟨rfl,ha⟩ := hmem
          refine ⟨hs,?_⟩
          simp
      · split at hmem
        · rename_i hs
          split at hmem
          · simp at hmem
          · simp only [List.mem_singleton,Prod.mk.injEq] at hmem
            obtain ⟨rfl,ha⟩ := hmem
            rcases hs with hs | hs <;> simp [hs] at hq
        · split at hmem
          · split at hmem
            · simp at hmem
            · simp only [List.mem_singleton,Prod.mk.injEq] at hmem
              obtain ⟨rfl,ha⟩ := hmem
              split at hq <;> norm_num at hq
          · split at hmem
            · simp at hmem
            · simp only [List.mem_singleton,Prod.mk.injEq] at hmem
              obtain ⟨rfl,ha⟩ := hmem
              norm_num at hq
  have go {s t : List ℤ} {xs : List (ℤ × ℤ × ℤ × ℤ)}
      (p : prefixRawAutomaton.Path s t xs) (ht : t[1]?.getD 0=0) :
      s[1]?.getD 0=0 ∧ (t[2]?.getD 0≠0 ↔ s[2]?.getD 0≠0 ∧
        ∀ z ∈ (pathOutputs (fun _ _ (q : List ℤ) => (baseTable (q[0]?.getD 0).toNat).1[10]?.getD 0) p).zip
          (pathOutputs (fun _ _ (q : List ℤ) => (baseTable (q[0]?.getD 0).toNat).1[12]?.getD 0) p),z.1+z.2=0) := by
    induction p with
    | nil s => exact ⟨ht,by simp [pathOutputs]⟩
    | cons q s t a xs he p ih =>
      have ih := ih ht
      have he' := back he ih.1
      refine ⟨he'.1,?_⟩
      rw [ih.2,he'.2]
      simp only [pathOutputs,List.zip_cons_cons,List.mem_cons,forall_eq_or_imp,Prod.fst,Prod.snd]
      tauto
  exact (go p ht).2

end D5.S1.Words.Palindromes.PeriodDoubling
#print axioms D5.S1.Words.Palindromes.PeriodDoubling.unmarked_path_flip_semantics
