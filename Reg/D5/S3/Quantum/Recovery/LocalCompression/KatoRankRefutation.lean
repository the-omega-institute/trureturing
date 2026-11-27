import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Recovery.LocalCompression.KatoRankRefutation

/-! Source-bound observation of the Choi marginal at the subtraction unitary. -/

namespace Reg.D5.S3.Quantum.Recovery.LocalCompression.KatoRankRefutation

open Matrix LeanInformationAudit
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Quantum.Recovery.LocalCompression.KatoRankRefutation
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open UnitaryReconstruction.LiuWildChoiObstruction (pairMatrix)

set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev signature := Reg.Support.SingleDependentReadout.signature ℕ
  (fun n => Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
  (fun n => Matrix (Fin n) (Fin n) ℂ)

noncomputable def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ X => partialTraceRight X) (fun a => nomatch a)

noncomputable def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 0) (fun a => nomatch a)

def arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ (n : ℕ) [NeZero n] (t : ℝ) (ht : 0 < t) (ht' : t < 1),
    (∀ p : Fin n × Fin n, 0 < weights t p) ∧
    (∀ a : Fin n, (∑ b : Fin n, weights t (a,b)) = (n : ℝ)⁻¹) ∧
    (∀ b : Fin n, (∑ a : Fin n, weights t (a,b)) = (n : ℝ)⁻¹) ∧
    (∀ X : Matrix (Fin n) (Fin n) ℂ,
      (∀ a, Commute X (pairMatrix ((experiment t ht ht').comparisonState a))) ↔
        X = diagonal X.diag) ∧
    (∀ X : Matrix (Fin n) (Fin n) ℂ,
      CStarMatrix.ofMatrix.symm ((dephasing n).toCompletelyPositiveMap
        (CStarMatrix.ofMatrix X)) = diagonal X.diag) ∧
    IsLeast (recoveryDimensions (n := n) t ht ht') n ∧
    choi n = diagonal (fun p => if p.1 = p.2 then (n : ℂ)⁻¹ else 0) ∧
    (∀ x y : Fin n, (subtractUnitary n : Matrix _ _ ℂ) *ᵥ Pi.single (x,y) 1 =
      Pi.single (x-y,y) 1) ∧
    R.readout () n ((subtractUnitary n : Matrix _ _ ℂ) * choi n *
      (subtractUnitary n : Matrix _ _ ℂ)ᴴ) =
      diagonal (fun i : Fin n => if i = 0 then 1 else 0) ∧
    marginalRank (subtractUnitary n) = 1 ∧
    IsLeast (Set.range (marginalRank (n := n))) 1

abbrev sourceScope := type_of% (@faithful_family)

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, _, _, _, _, _, _, _, hm, _, _⟩ :=
    h 2 (1 / 2) (by norm_num) (by norm_num)
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hm
  simpa [rejected, DependentFamily.realize] using h00

private theorem actual_dependence : DependentFamily.ObservationalDependence signature actual := by
  intro i
  cases i
  let X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
    (subtractUnitary 2 : Matrix _ _ ℂ) * choi 2 * (subtractUnitary 2 : Matrix _ _ ℂ)ᴴ
  refine ⟨2, 0, X, ?_⟩
  intro heq
  obtain ⟨_, _, _, _, _, _, _, _, hm, _, _⟩ :=
    faithful_family 2 (1 / 2) (by norm_num) (by norm_num)
  change partialTraceRight (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) =
    partialTraceRight X at heq
  rw [show partialTraceRight X = diagonal (fun j : Fin 2 => if j = 0 then 1 else 0) from hm] at heq
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) heq
  simpa [partialTraceRight] using h00

noncomputable def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨faithful_family, rejected, rejected_fails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_fails
  dependence := actual_dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@faithful_family) (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.LocalCompression.KatoRankRefutation.faithful_family.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.LocalCompression.KatoRankRefutation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature
    (fun _ _ X => partialTraceRight X) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.LocalCompression.KatoRankRefutation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Recovery.LocalCompression.KatoRankRefutation
