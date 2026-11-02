import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Foundation.ApproximateOrientedAnchorRepair
import Reg.Support.SingleDependentReadout

/-! Full-telescope dependent-readout registration for finite oriented anchor repair. -/

noncomputable section
universe u v
open scoped InnerProductSpace ComplexOrder Ring
open Complex
open _root_.D5.S3.Quantum.Foundation.ApproximateOrientedAnchorRepair
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Foundation.ApproximateOrientedAnchorRepair

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {H : Type u} {W : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    {d : ℕ} (hd : 1 ≤ d) (a : OrthonormalBasis (Fin d) ℂ H) (F : H → W)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hN : ∀ x, ‖x‖ = 1 → ‖F x‖ = 1)
    (hphase : ∀ j (k : Fin 4), F ((I ^ (k : ℕ)) • a j) = (I ^ (k : ℕ)) • F (a j))
    (hcomp : ∀ x, ‖x‖ = 1 → ∀ j (k : Fin 4),
      ‖F x - F ((I ^ (k : ℕ)) • a j)‖ ^ 2 ≤
        ‖x - (I ^ (k : ℕ)) • a j‖ ^ 2 + δ)
    (hsmall : kappa d δ < 1),
    let B := basisExtension a F
    let G := B.adjoint.comp B
    IsStrictlyPositive G ∧
      ∃ U : H →ₗᵢ[ℂ] W,
        U.toContinuousLinearMap = B.comp (CFC.sqrt G)⁻¹ʳ ∧
        ‖G - 1‖ ≤ kappa d δ ∧
        ‖B - U.toContinuousLinearMap‖ ≤ 1 - Real.sqrt (1 - kappa d δ) ∧
        ∀ x, ‖x‖ = 1 →
          R.readout () () ‖F x - U x‖
            (min 2 (Real.sqrt (kappa d δ + 2 * eta d δ) + 1 - Real.sqrt (1 - kappa d δ)))

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  classical
  intro h
  let J := ULift.{u} Unit
  let K := ULift.{v} Unit
  let H := EuclideanSpace ℂ J
  let W := EuclideanSpace ℂ K
  let a : OrthonormalBasis (Fin 1) ℂ H :=
    (EuclideanSpace.basisFun J ℂ).reindex (Equiv.ulift.trans finOneEquiv.symm)
  let V : H ≃ₗᵢ[ℂ] W :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.ulift.trans Equiv.ulift.symm)
  have hN : ∀ x : H, ‖x‖ = 1 → ‖V x‖ = 1 := fun x hx => (V.norm_map x).trans hx
  have hp : ∀ j (k : Fin 4), V ((I ^ (k : ℕ)) • a j) =
      (I ^ (k : ℕ)) • V (a j) := fun j k => V.map_smul _ _
  have hc : ∀ x : H, ‖x‖ = 1 → ∀ j (k : Fin 4),
      ‖V x - V ((I ^ (k : ℕ)) • a j)‖ ^ 2 ≤
        ‖x - (I ^ (k : ℕ)) • a j‖ ^ 2 + (0 : ℝ) := by
    intro x hx j k
    rw [← V.map_sub, V.norm_map, add_zero]
  have hs : kappa 1 0 < 1 := by norm_num [kappa]
  have hh := @h H W _ _ _ _ _ _ 1 (by omega) a V 0 (by norm_num) hN hp hc hs
  obtain ⟨_, U, _, _, _, hbad⟩ := hh
  exact hbad (a 0) (a.norm_eq_one 0)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 0
  norm_num [actual, realize] at h

def family : Registration arena.{u,v}
    (type_of% @finite_oriented_anchor_polar_repair.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_oriented_anchor_polar_repair, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_oriented_anchor_polar_repair.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Foundation.ApproximateOrientedAnchorRepair.finite_oriented_anchor_polar_repair.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.ApproximateOrientedAnchorRepair.family
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
    owner := `D5.S3.Quantum.Foundation.ApproximateOrientedAnchorRepair
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "arg", "arg", "arg", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Foundation.ApproximateOrientedAnchorRepair
