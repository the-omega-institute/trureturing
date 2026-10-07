/- GID: D5/S1/Words/Palindromes/PeriodDoubling/SignedDigitPhase
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/SignedDigitPhase
   mirror-E: none(waiver:literal-signed-tail-negative-phase)
   anchors: []
   utility: none
   digest: The last nonzero signed digit fixes the negative phase of a binary tail. -/

/-
proof_shape: content (signed_digits_negative_phase)
escape_witness: Signed-digit induction proves sign dominance, including both empty-tail parity cases.
admission_basis: escape-witness
Direct frozen dependencies: none.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Data.Int.Basic
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Palindromes.PeriodDoubling

theorem signed_digits_negative_phase (ds : List ℤ) (delta : Bool)
    (hc : ∀ z ∈ ds, z=-1 ∨ z=0 ∨ z=1) :
    (2*ds.foldr (fun z x => z+2*x) 0-(delta.toNat : ℤ) < 0) ↔
    ((ds.filter (fun z => z != 0)).getLast?.getD 0 < 0 ∨
      (ds.filter (fun z => z != 0))=[] ∧ delta=true) := by
  induction ds generalizing delta with
  | nil => cases delta <;> simp
  | cons d ds ih =>
    have hd:=hc d (by simp)
    have ht : ∀ z ∈ ds, z=-1 ∨ z=0 ∨ z=1 := fun z hz => hc z (by simp [hz])
    have hempty : (ds.filter (fun z => z != 0))=[] → ds.foldr (fun z x => z+2*x) 0=0 := by
      intro he
      have hzero : ∀ z ∈ ds, z=0 := by
        intro z hz
        have hh:=(List.filter_eq_nil_iff.mp he) z hz
        simpa using hh
      clear hc ht hd ih
      induction ds with
      | nil => rfl
      | cons a ds ih =>
        have ha:=hzero a (by simp)
        simp only [List.foldr_cons,ha,Int.zero_add]
        rw [ih (by simpa [ha] using he) (fun z hz => hzero z (by simp [hz]))]
        simp
    have ih0:=ih false ht
    have ih1:=ih true ht
    by_cases he : (ds.filter (fun z => z != 0))=[]
    · have hv:=hempty he
      rcases hd with hd | hd | hd <;> subst d <;> cases delta <;> simp [List.filter_cons,he,hv]
    · have hlast : ((d::ds).filter (fun z => z != 0)).getLast?=(ds.filter (fun z => z != 0)).getLast? := by
        by_cases hd0 : d=0
        · simp [hd0]
        · simp only [List.filter_cons,bne_iff_ne]
          rw [if_pos hd0]
          exact List.getLast?_cons_of_ne_nil he
      have hn : ((d::ds).filter (fun z => z != 0)) ≠ [] := by
        simp only [List.filter_cons]
        split <;> simp_all
      rw [hlast]
      simp only [hn,false_and,or_false]
      simp only [he,false_and,or_false] at ih0 ih1
      rcases hd with hd | hd | hd <;> subst d <;> cases delta <;>
        simp only [List.foldr_cons,Bool.toNat_false,Bool.toNat_true,Int.natCast_zero,Int.natCast_one] at * <;> omega

end D5.S1.Words.Palindromes.PeriodDoubling
#print axioms D5.S1.Words.Palindromes.PeriodDoubling.signed_digits_negative_phase
