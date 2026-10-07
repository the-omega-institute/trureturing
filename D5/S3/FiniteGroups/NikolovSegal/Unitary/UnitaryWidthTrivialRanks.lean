/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthTrivialRanks
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthTrivialRanks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryWidthRankTwo

set_option autoImplicit false
namespace NikolovSegal.UnitaryWholeGroupWidth
open Matrix UnitarySylow
universe u
variable {F : Type u} [Field F] {n : ℕ} {ι : RingAut F}

/-- The exact requested ordered carrier endpoint in ranks zero and one. -/
theorem trivial_alternating_25 [Subsingleton (Fin n)] (g : specialUnitary n ι) :
    ∃ a : Fin 25 → specialUnitary n ι,
      (∀ j, if j.val % 2 = 0 then
        ∀ r c : Fin n, c.val < r.val+1 → ((a j).val.val-1) r c=0
      else ∀ r c : Fin n, r.val < c.val+1 → ((a j).val.val-1) r c=0) ∧
      (List.ofFn a).prod=g := by
  refine ⟨fun _ => 1,?_,?_⟩
  · intro j; split <;> intro r c h <;> simp
  · exact Subsingleton.elim _ _

end NikolovSegal.UnitaryWholeGroupWidth
