import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.CenteredTopEigenvectorObstruction
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Estimation.CenteredTopEigenvectorObstruction

open _root_.D5.S3.Estimation.CenteredTopEigenvectorObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Matrix
open scoped RealInnerProductSpace

set_option autoImplicit false
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- The original statement is retained; the readout observes the half-trace bound for positive
semidefinite matrices. -/
abbrev arena : Arena where
  signature := signature
  Law Q := ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian)
    (u v : EuclideanSpace ℝ (Fin n)), ‖u‖ = 1 → ‖v‖ = 1 → ∀ (l : ℝ),
    H.toEuclideanLin v = l • v →
    (∀ (m : ℝ) (x : EuclideanSpace ℝ (Fin n)), x ≠ 0 → H.toEuclideanLin x = m • x → m ≤ l) →
    ⟪u, v⟫ ^ 2 ≤ 1 / 2 →
    (0 ≤ ⟪u, H.toEuclideanLin u⟫ - H.trace / n →
      2 * n * (⟪u, H.toEuclideanLin u⟫ - H.trace / n) ^ 2 ≤
        (n - 2) * ((H - (H.trace / n) • (1 : Matrix (Fin n) (Fin n) ℝ)) *
          (H - (H.trace / n) • 1)).trace) ∧
    (H.PosSemidef → Q.readout () () ⟪u, H.toEuclideanLin u⟫ (H.trace / 2))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hu : ‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ = 1 := by simp
  have hv : ‖EuclideanSpace.single (1 : Fin 2) (1 : ℝ)‖ = 1 := by simp
  have huv : ⟪EuclideanSpace.single (0 : Fin 2) (1 : ℝ),
      EuclideanSpace.single (1 : Fin 2) (1 : ℝ)⟫ ^ 2 ≤ 1 / 2 := by
    simp [EuclideanSpace.inner_single_left]
  have heig : (0 : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin
      (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) =
        (0 : ℝ) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := by simp
  have htop : ∀ (m : ℝ) (x : EuclideanSpace ℝ (Fin 2)), x ≠ 0 →
      (0 : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin x = m • x → m ≤ 0 := by
    intro m x hx hm
    simp only [map_zero, LinearMap.zero_apply] at hm
    rcases smul_eq_zero.mp hm.symm with h | h
    · exact h.le
    · exact absurd h hx
  exact (h (0 : Matrix (Fin 2) (Fin 2) ℝ) Matrix.isHermitian_zero _ _ hu hv 0 heig htop
    huv).2 Matrix.PosSemidef.zero

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 0, ?_⟩
  intro h
  have hh := congrFun h (0 : ℝ)
  norm_num [actual, realize] at hh

def family : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result) (Realization signature) Unit Unit where
  unitName := `D5.S3.Estimation.CenteredTopEigenvectorObstruction.result.__information_unit
  realizationName := `Reg.D5.S3.Estimation.CenteredTopEigenvectorObstruction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Estimation.CenteredTopEigenvectorObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Estimation.CenteredTopEigenvectorObstruction
