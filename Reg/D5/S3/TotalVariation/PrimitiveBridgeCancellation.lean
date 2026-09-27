import D5.S3.TotalVariation.PrimitiveBridgeCancellation
import Reg.Support.DependentFamily

open _root_.D5.S3.TotalVariation.PrimitiveBridgeCancellation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
open Quiver Quiver.Path

noncomputable section
namespace Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation
universe u

abbrev signature : Signature where
  Params := Σ q : ℕ, Finset (Fin q → ℤ)
  State p := Fin p.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Energy of the very same finite generating set selected by the source existential. -/
def actual : Realization signature :=
  realize signature (fun _ p x => energy p.2 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Only the energy occurrence in the cancellation inequality is selected. All other
clauses retain the common bridge length, generators, coefficient and actual paths. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hstoch : P ∈ Matrix.rowStochastic ℝ V)
    (hprim : Matrix.IsPrimitive P) {q : ℕ} (g : V → V → (Fin q → ℤ))
    (iStar jStar : V),
    letI : Quiver V := Matrix.toQuiver P
    ∃ L : ℕ, 0 < L ∧ ∃ F : Finset (Fin q → ℤ), ∃ c : ℝ, 0 < c ∧
      Submodule.span ℤ (F : Set (Fin q → ℤ)) = lattice P g ∧
      (∀ lam ∈ F, ∃ a b : Gamma P L iStar jStar,
        a.val.addWeightOfEPs g - b.val.addWeightOfEPs g = lam ∧
        c ≤ a.val.weightOfEPs (fun i j => P i j) * b.val.weightOfEPs (fun i j => P i j)) ∧
      0 < (P ^ L) iStar jStar ∧
      (∀ x : Fin q → ℝ, c * r.readout () ⟨q, F⟩ x ≤
        ((P ^ L) iStar jStar)^2 - ‖(twisted P g x ^ L) iStar jStar‖^2) ∧
      (∀ x : Fin q → ℝ, energy F x = 0 ↔ x ∈ annihilator P g)

/-- A one-state primitive stochastic chain with zero charges has zero deficit at
all lengths, so no positive coefficient can support the constant-one intervention. -/
theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let V := ULift.{u} Unit
  let P : Matrix V V ℝ := 1
  have hp : Matrix.IsPrimitive P := by
    constructor
    · intro i j
      simp [P, Matrix.one_apply, Subsingleton.elim i j]
    · exact ⟨1, by omega, by intro i j; simp [P, Matrix.one_apply, Subsingleton.elim i j]⟩
  obtain ⟨L, hL, F, c, hc, hspan, hpaths, hpos, hcancel, hann⟩ :=
    h P (Matrix.rowStochastic ℝ V).one_mem hp (q := 1) (fun _ _ _ => 0) ⟨()⟩ ⟨()⟩
  have ht : twisted P (fun _ _ => fun _ : Fin 1 => (0 : ℤ)) (fun _ => 0) =
      (1 : Matrix V V ℂ) := by
    ext i j
    simp [twisted, dot, P, Matrix.one_apply, Subsingleton.elim i j]
  have hh := hcancel (fun _ => 0)
  simp only [ht, P, one_pow, Matrix.one_apply_eq, norm_one,
    one_pow, sub_self] at hh
  have : c ≤ 0 := by simpa [rejected, realize] using hh
  exact (not_le_of_gt hc) this

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, {fun _ : Fin 1 => (1 : ℤ)}⟩, (fun _ => 0), (fun _ => Real.pi), ?_⟩
  norm_num [actual, realize, energy, dot, Fin.sum_univ_one]

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.TotalVariation.PrimitiveBridgeCancellation.primitive_bridge_cancellation.{u},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

register_information_theorem
  _root_.D5.S3.TotalVariation.PrimitiveBridgeCancellation.primitive_bridge_cancellation in arena
  readout via (realize signature (fun _ p x => energy p.2 x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.TotalVariation.PrimitiveBridgeCancellation
    coordinates := #[7, 12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "fn", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 14 }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation
