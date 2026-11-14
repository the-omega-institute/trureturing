import D5.S3.ArithSums.MatharA386830
import Reg.Support.DependentFamily

/-! A typed whole-family realization for the literal sequence.
Outer source-occurrence binding is unfinished under https://github.com/the-omega-institute/trureturing/issues/30405. -/

namespace Reg.D5.S3.ArithSums.MatharA386830

open _root_.D5.S3.ArithSums.MatharA386830
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    let seq := R.readout () ()
    (∀ n : ℕ, 2 ≤ n →
      8*(n : ℤ)*(2*(n : ℤ)-3)*seq n +
      6*(-108*(n : ℤ)^2+207*(n : ℤ)-80)*seq (n-1) +
      405*(3*(n : ℤ)-2)*(3*(n : ℤ)-4)*seq (n-2) = 0) ∧
    (∃ r : ℕ, ∃ p : ℕ → Polynomial ℚ,
      (∃ j ∈ Finset.range (r+1), p j ≠ 0) ∧
      ∑ j ∈ Finset.range (r+1), (p j : PowerSeries ℚ) *
        (PowerSeries.derivative (R := ℚ))^[j]
          (PowerSeries.mk fun n => (seq n : ℚ)) = 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h2 := h.1 2 (by omega)
  norm_num [rejected, realize] at h2

def family : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize, a, Finset.sum_range_succ, Nat.choose]

#print axioms family

end
end Reg.D5.S3.ArithSums.MatharA386830
