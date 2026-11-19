import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.UmegakiFaithfulLowerRatio

/-! The actual approximation inequality is the readout, with the full density-pair telescope. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix
open scoped Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteDiamondDistance
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open _root_.D5.S3.Quantum.Divergence.UmegakiFaithfulLowerRatio
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Divergence.UmegakiFaithfulLowerRatio
universe ur ua ub

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r : Type ur} {a : Type ua} {b : Type ub}
    [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (N : QuantumChannel a b) (hN : (act N (1 : Matrix a a ℂ)).PosDef)
    (Z V : Matrix (r × a) (r × a) ℂ) (hZ : Z.PosDef)
    (hV : partialTraceRight V = 0)
    (hqin : 0 < (Vᴴ * Z⁻¹ * V).trace.re) (η : ℝ) (hη : 0 < η),
    ∃ rho sigma : DensityState ((Fin 2 × r) × a),
      (CStarMatrix.ofMatrix.symm rho.1).PosDef ∧
      (CStarMatrix.ofMatrix.symm sigma.1).PosDef ∧
      (CStarMatrix.ofMatrix.symm (referenceState N rho).1).PosDef ∧
      (CStarMatrix.ofMatrix.symm (referenceState N sigma).1).PosDef ∧
      marginalRight rho = marginalRight sigma ∧
      marginalRight (referenceState N rho) = marginalRight (referenceState N sigma) ∧
      SupportContained rho sigma ∧
      SupportContained (referenceState N rho) (referenceState N sigma) ∧
      0 < finiteTraceLogRelativeEntropy rho sigma ∧
      R.readout () () |finiteTraceLogRelativeEntropy (referenceState N rho) (referenceState N sigma) /
          finiteTraceLogRelativeEntropy rho sigma -
        ( (amp N V)ᴴ * (amp N Z)⁻¹ * amp N V).trace.re /
          (Vᴴ * Z⁻¹ * V).trace.re| η ∧
      finiteTraceLogRelativeEntropy (referenceState N rho) (referenceState N sigma) -
          finiteTraceLogRelativeEntropy (marginalRight (referenceState N rho))
            (marginalRight (referenceState N sigma)) =
        finiteTraceLogRelativeEntropy (referenceState N rho) (referenceState N sigma)

private theorem rejected_law : ¬ arena.{ur,ua,ub}.Law rejected := by
  intro h
  let r := ULift.{ur} Unit
  let a := ULift.{ua} (Fin 2)
  let b := ULift.{ub} (Fin 2)
  let E : a ≃ b := Equiv.ulift.trans Equiv.ulift.symm
  let N : QuantumChannel a b := {
    toCompletelyPositiveMap := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
      (CStarMatrix.reindexₐ ℂ ℂ E)
    trace_preserving := by
      intro X
      exact E.symm.sum_comp (fun i => X i i) }
  have hN : (act N (1 : Matrix a a ℂ)).PosDef := by
    change (CStarMatrix.ofMatrix.symm ((CStarMatrix.reindexₐ ℂ ℂ E) 1)).PosDef
    rw [map_one]
    exact Matrix.PosDef.one
  let V : Matrix (r × a) (r × a) ℂ :=
    Matrix.diagonal (fun p => if p.2.down = 0 then (1:ℂ) else -1)
  have hp : partialTraceRight V = 0 := by
    ext i j
    change (∑ x : a, V (i,x) (j,x)) = (0 : ℂ)
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp only [V, Matrix.diagonal_apply, ite_true]
    rw [← (Equiv.ulift : a ≃ Fin 2).symm.sum_comp
      (fun x : a => if x.down = 0 then (1:ℂ) else -1)]
    norm_num [Fin.sum_univ_two]
  have hs : Vᴴ = V := by
    simp only [V, Matrix.diagonal_conjTranspose]
    congr 1
    funext p
    dsimp only [Pi.star_apply]
    split_ifs <;> simp
  have hv : V*V = 1 := by
    rw [show V = Matrix.diagonal (fun p => if p.2.down = 0 then (1:ℂ) else -1) from rfl,
      Matrix.diagonal_mul_diagonal]
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> norm_num
  have hq : 0 < (Vᴴ * (1 : Matrix (r × a) (r × a) ℂ)⁻¹ * V).trace.re := by
    rw [inv_one, Matrix.mul_one, hs, hv]
    norm_num [Matrix.trace_one, r, a]
  obtain ⟨rho, sigma, _, _, _, _, _, _, _, _, _, bad, _⟩ :=
    h N hN 1 V Matrix.PosDef.one hp hq 1 zero_lt_one
  exact bad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 1
  norm_num [actual, realize] at hh

def family : Registration arena.{ur,ua,ub} (type_of% @faithful_density_pair_ratio_approx) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@faithful_density_pair_ratio_approx, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@faithful_density_pair_ratio_approx) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiFaithfulLowerRatio.faithful_density_pair_ratio_approx.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiFaithfulLowerRatio.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{ur,ua,ub}⟩
  objectArena := .source ⟨arena.{ur,ua,ub}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{ur,ua,ub} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiFaithfulLowerRatio
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg",
        "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms faithful_density_pair_ratio_approx
#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.UmegakiFaithfulLowerRatio
