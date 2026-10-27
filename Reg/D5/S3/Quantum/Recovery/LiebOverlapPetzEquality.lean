import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.LiebOverlapPetzEquality
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability

/-! Faithful registration attempt for one fixed completed Petz recovery. -/

noncomputable section
universe u v
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open _root_.D5.S3.Quantum.Divergence.CanonicalChannelDPI
open _root_.D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open _root_.D5.S3.Quantum.Recovery.LiebOverlapPetzEquality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Recovery.LiebOverlapPetzEquality

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Prop) (fun _ => Prop → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ∧ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (Phi : QuantumChannel a b) (sigma : DensityState a),
    let K := (actual_kraus_representation Phi).kraus
    let S := cfc Real.sqrt (CStarMatrix.ofMatrix.symm sigma.1)
    let Q := CStarMatrix.ofMatrix.symm (Phi.mapState sigma).1
    let W := spectralInverseSqrt Q
    let P := spectralSupport Q
    ∃ recovery : QuantumChannel b a,
      (∀ X : Matrix b b ℂ,
        CStarMatrix.ofMatrix.symm
          (recovery.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
          (∑ c, S * (K c)ᴴ * W * X * W * K c * S) +
            Matrix.trace ((1 - P) * X) • CStarMatrix.ofMatrix.symm sigma.1) ∧
      recovery.mapState (Phi.mapState sigma) = sigma ∧
      ∀ (rho : DensityState a) (support : SupportContained rho sigma)
        (q : ℝ), 0 < q → q < 1 →
        let inputOverlap := (cfc (fun x : ℝ => x ^ (1 - q))
            (CStarMatrix.ofMatrix.symm rho.1) *
          cfc (fun x : ℝ => x ^ q) (CStarMatrix.ofMatrix.symm sigma.1)).trace.re
        let outputOverlap := (cfc (fun x : ℝ => x ^ (1 - q))
            (CStarMatrix.ofMatrix.symm (Phi.mapState rho).1) *
          cfc (fun x : ℝ => x ^ q)
            (CStarMatrix.ofMatrix.symm (Phi.mapState sigma).1)).trace.re
        R.readout () ()
          (outputOverlap = inputOverlap ↔
            finiteTraceLogRelativeEntropy rho sigma =
              finiteTraceLogRelativeEntropy (Phi.mapState rho) (Phi.mapState sigma))
          (outputOverlap = inputOverlap ↔ recovery.mapState (Phi.mapState rho) = rho)

set_option maxHeartbeats 0 in
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  apply _root_.Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.rejected_law
  intro a b ia da na ib db nb Phi rho sigma support m hm
  let M := supported_relative_modular_model Phi rho sigma support
  change m • 1 ≤ M.data.A → m • 1 ≤ M.data.B → False
  intro hfloorA hfloorB
  obtain ⟨recovery, haction, hreference, hfalse⟩ := @h a b ia da na ib db nb Phi sigma
  exact hfalse rho support (1 / 2) (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have h := congrFun he True
  simp [actual, realize] at h

def family : Registration arena.{u,v}
    (type_of% @actual_lieb_overlap_equality_iff_fixed_petz_recovery.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_lieb_overlap_equality_iff_fixed_petz_recovery, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_lieb_overlap_equality_iff_fixed_petz_recovery.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.LiebOverlapPetzEquality.actual_lieb_overlap_equality_iff_fixed_petz_recovery.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.LiebOverlapPetzEquality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ∧ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.LiebOverlapPetzEquality
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Recovery.LiebOverlapPetzEquality
