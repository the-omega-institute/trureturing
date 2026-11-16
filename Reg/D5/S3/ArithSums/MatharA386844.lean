import D5.S3.ArithSums.MatharA386844
import Reg.Support.DependentFamily

/-! Source-family evidence for the literal summand and the entire native conjunction.
The outer source-occurrence binding is unfinished: https://github.com/the-omega-institute/trureturing/issues/27973. -/

namespace Reg.D5.S3.ArithSums.MatharA386844

open _root_.D5.S3.ArithSums.MatharA386844
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ n k => (3*n+2).choose k * (3*n-k).choose (n-k))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def sequence (R : Realization signature) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n+1), R.readout () n k

/-- Reconstruct both recurrences and the same complete ordinary series from one readout. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    let b := sequence R
    (∀ n : ℕ, 3 ≤ n →
      let m : ℤ := n
      3*m*(2*m-1)*(b n : ℤ) + (-353*m^2+1009*m-672)*(b (n-1) : ℤ) +
        (3938*m^2-15029*m+13872)*(b (n-2) : ℤ) -
        399*(3*m-4)*(3*m-5)*(b (n-3) : ℤ) = 0) ∧
    (∀ n : ℕ, 2 ≤ n →
      let m : ℤ := n
      m*(2*m-1)*(5*m-8)*(b n : ℤ) +
        (-145*m^3+362*m^2-264*m+63)*(b (n-1) : ℤ) +
        3*(3*m-1)*(5*m-3)*(3*m-2)*(b (n-2) : ℤ) = 0) ∧
    (∃ r : ℕ, ∃ p : Fin (r+1) → Polynomial ℚ,
      (∃ j, p j ≠ 0) ∧ op r p (PowerSeries.mk fun n => (b n : ℚ)) = 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.2.1 2 (by omega)
  norm_num [sequence, rejected, realize, Finset.sum_range_succ] at hb

def source_registration : Registration arena P where
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
    refine ⟨1, 0, 1, ?_⟩
    norm_num [actual, realize, Nat.choose]

end
end Reg.D5.S3.ArithSums.MatharA386844
