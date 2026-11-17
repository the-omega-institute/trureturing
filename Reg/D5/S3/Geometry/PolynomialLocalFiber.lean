import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.PolynomialLocalFiber

/-! The maximal-rank comparison is observed on its complete polynomial and
local-fiber telescope. Interventions change the comparison on the whole family. -/

noncomputable section
open Set Metric MvPolynomial LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.PolynomialLocalFiber

namespace Reg.D5.S3.Geometry.PolynomialLocalFiber

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ r s => r ≤ s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℝ),
    ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
      (∃ a₀ : Fin n → ℝ, eval a₀ D = 1) ∧
      ∀ a : Fin n → ℝ, eval a D ≠ 0 →
        (∀ x : Fin n → ℝ,
          R.readout () ()
            (Module.finrank ℝ (LinearMap.range
              (fderiv ℝ (fun y j => eval y (p j)) x).toLinearMap))
            (Module.finrank ℝ (LinearMap.range
              (fderiv ℝ (fun y j => eval y (p j)) a).toLinearMap))) ∧
        ∀ U : Set (Fin n → ℝ), IsOpen U → a ∈ U →
          ∃ (K : Submodule ℝ (Fin n → ℝ)) (q : (Fin n → ℝ) →L[ℝ] K)
            (k : K → (Fin n → ℝ)) (ε : ℝ),
            0 < ε ∧
            Module.finrank ℝ K +
              Module.finrank ℝ (LinearMap.range
                (fderiv ℝ (fun y j => eval y (p j)) a).toLinearMap) = n ∧
            k 0 = a ∧ ContDiffOn ℝ 1 k (ball 0 ε) ∧
            (∀ z ∈ ball 0 ε, k z ∈ U ∧
              (∀ j, eval (k z) (p j) = eval a (p j)) ∧ q (k z - a) = z) ∧
            (m < n → 0 < Module.finrank ℝ K ∧
              ∃ b ∈ U, b ≠ a ∧ ∀ j, eval b (p j) = eval a (p j))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨D, _, ⟨a₀, ha₀⟩, hD⟩ := h (n := 0) (m := 0) (fun _ => 0)
  exact (hD a₀ (by rw [ha₀]; norm_num)).1 a₀

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have bad := congrFun h 0
  change ((0 : ℕ) ≤ 0) = ((1 : ℕ) ≤ 0) at bad
  have : (1 : ℕ) ≤ 0 := Eq.mp bad (le_refl 0)
  omega

def family : Registration arena (type_of% (@exists_rank_fiber_polynomial)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_rank_fiber_polynomial, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_rank_fiber_polynomial) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.PolynomialLocalFiber.unit
  realizationName := `Reg.D5.S3.Geometry.PolynomialLocalFiber.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ r s => r ≤ s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.PolynomialLocalFiber
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "arg",
        "body", "body", "fn", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.PolynomialLocalFiber
