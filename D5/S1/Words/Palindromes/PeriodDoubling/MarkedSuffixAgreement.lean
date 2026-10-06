/- GID: D5/S1/Words/Palindromes/PeriodDoubling/MarkedSuffixAgreement
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/MarkedSuffixAgreement
   mirror-E: none(waiver:unbounded-marker-suffix-agreement)
   anchors: []
   utility: none
   digest: A valid completed marker keeps every higher signed digit and its stored phase data. -/

/-
proof_shape: content (marked_suffix_agreement)
escape_witness: Backward propagation of the terminal flag reconstructs agreement at every position.
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
open MarkedPrefixCertificates

/-- A good terminal flag forces all coefficients above a selected marker to match. -/
theorem marked_suffix_agreement {s t : List ℤ} {xs : List (ℤ × ℤ × ℤ × ℤ)}
    (p : prefixRawAutomaton.Path s t xs)
    (hs : s[1]?.getD 0=1 ∨ s[1]?.getD 0=2 ∨ s[1]?.getD 0=3 ∨ s[1]?.getD 0=4)
    (ht : t[7]?.getD 0=0) :
    s[7]?.getD 0=0 ∧
    pathOutputs (fun _ _ (q : List ℤ) => (BaseCertificates.baseTable (q[0]?.getD 0).toNat).1[10]?.getD 0) p =
      pathOutputs (fun _ _ (q : List ℤ) => (BaseCertificates.baseTable (q[0]?.getD 0).toNat).1[12]?.getD 0) p ∧
    (∀ k : ℕ, 3≤k → k≤6 → t[k]?.getD 0=s[k]?.getD 0) := by
  have step {s q : List ℤ} {a : ℤ × ℤ × ℤ × ℤ}
      (he : (q,a) ∈ successors s)
      (hs : s[1]?.getD 0=1 ∨ s[1]?.getD 0=2 ∨ s[1]?.getD 0=3 ∨ s[1]?.getD 0=4) :
      (q[1]?.getD 0=1 ∨ q[1]?.getD 0=2 ∨ q[1]?.getD 0=3 ∨ q[1]?.getD 0=4) ∧
      (q[7]?.getD 0=0 → s[7]?.getD 0=0 ∧
        (BaseCertificates.baseTable (q[0]?.getD 0).toNat).1[10]?.getD 0 =
          (BaseCertificates.baseTable (q[0]?.getD 0).toNat).1[12]?.getD 0) ∧
      (∀ k : ℕ, 3≤k → k≤6 → q[k]?.getD 0=s[k]?.getD 0) := by
    obtain ⟨e,he,hmem⟩ := List.mem_flatMap.mp he
    unfold nextMarker at hmem
    dsimp only at hmem
    rcases hs with hs | hs | hs | hs <;> simp only [hs] at hmem <;>
      norm_num only at hmem <;> simp only [ite_true,ite_false,true_or,false_or] at hmem
    all_goals
      split at hmem
      · simp at hmem
    all_goals
      split at hmem
      · simp at hmem
      · simp only [List.mem_singleton,Prod.mk.injEq] at hmem
        obtain ⟨rfl,ha⟩ := hmem
        constructor
        · simp <;> split <;> simp_all
        · constructor
          · intro hbad
            simpa using hbad
          · intro k hk hl
            have hcases : k=3 ∨ k=4 ∨ k=5 ∨ k=6 := by omega
            rcases hcases with rfl | rfl | rfl | rfl <;> rfl
  revert hs ht
  induction p with
  | nil s =>
    intro hs ht
    exact ⟨ht,rfl,fun _ _ _ => rfl⟩
  | cons q s t a xs he p ih =>
    intro hs ht
    obtain ⟨hmode,hflag,hmem⟩ := step he hs
    obtain ⟨hq,hdigits,hend⟩ := ih hmode ht
    obtain ⟨hsflag,hd⟩ := hflag hq
    refine ⟨hsflag,?_,?_⟩
    · simp only [pathOutputs,hd,hdigits]
    · intro k hk hl
      exact (hend k hk hl).trans (hmem k hk hl)

end D5.S1.Words.Palindromes.PeriodDoubling
#print axioms D5.S1.Words.Palindromes.PeriodDoubling.marked_suffix_agreement
