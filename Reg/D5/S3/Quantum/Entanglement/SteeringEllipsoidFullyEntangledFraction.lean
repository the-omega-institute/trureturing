import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
  (pauliMatrix Pauli)
open _root_.D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open _root_.D5.S3.QuantumBounds.CHSHWitness renaming TwoQubitMatrix → TwoQubit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped Kronecker ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace VectorLength

/-- Observe the Euclidean length of the input vector. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 3 → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ v => vlen v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ v : Fin 3 → ℝ,
    R.readout () () v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3))‖

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0
  change (1 : ℝ) = ‖(WithLp.toLp 2 (0 : Fin 3 → ℝ) : EuclideanSpace ℝ (Fin 3))‖ at he
  norm_num at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, ![0, 0, 1], ?_⟩
  change vlen 0 ≠ vlen ![0, 0, 1]
  rw [vlen_e3]
  norm_num [vlen]

def source_registration : Registration arena (type_of% @vlen_eq_norm) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨vlen_eq_norm, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

end VectorLength

namespace BlochVector

/-- Observe the Pauli trace vector of the input matrix. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Matrix (Fin 2) (Fin 2) ℂ) (fun _ => Fin 3 → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ Z => blochVec Z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ![0, 0, 1]) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (Z : Matrix (Fin 2) (Fin 2) ℂ) (_hZ : Z.IsHermitian),
    WithLp.toLp 2 (R.readout () () Z) =
      _root_.D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch Z

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 0 (by simp)).trans (blochVec_eq_bloch 0 (by simp)).symm
  have hc := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) he
  change (1 : ℝ) = blochVec (0 : Matrix (Fin 2) (Fin 2) ℂ) 2 at hc
  norm_num [blochVec] at hc

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, !![1, 0; 0, 0], ?_⟩
  intro he
  have hc := congrArg (fun v : Fin 3 → ℝ => v 2) he
  have hpauli : pauli (2 : Fin 3) = !![1, 0; 0, -1] := by rfl
  change blochVec (0 : Matrix (Fin 2) (Fin 2) ℂ) 2 = blochVec !![1, 0; 0, 0] 2 at hc
  norm_num [blochVec, hpauli, trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.vecMul, dotProduct] at hc

def source_registration : Registration arena (type_of% @blochVec_eq_bloch) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨blochVec_eq_bloch, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

end BlochVector

namespace AliceTrace

/-- Observe the marginal trace paired with Alice's matrix coefficient. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature TwoQubit
    (fun _ => Matrix (Fin 2) (Fin 2) ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ ρ A => trace (partialTraceRight ρ * A)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (ρ : TwoQubit) (A : Matrix (Fin 2) (Fin 2) ℂ),
    trace (ρ * (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))) = R.readout () ρ A

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0 0
  norm_num [rejected, realize] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change trace (partialTraceRight (1 : TwoQubit) * 0) ≠
    trace (partialTraceRight (1 : TwoQubit) * 1)
  rw [mul_zero, trace_zero, mul_one, trace_partialTraceRight]
  norm_num [trace_one]

def source_registration : Registration arena (type_of% @trace_mul_kron_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨trace_mul_kron_one, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

end AliceTrace

namespace BobTrace

/-- Observe the marginal trace paired with Bob's matrix coefficient. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature TwoQubit
    (fun _ => Matrix (Fin 2) (Fin 2) ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ ρ B => trace (partialTraceLeft ρ * B)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (ρ : TwoQubit) (B : Matrix (Fin 2) (Fin 2) ℂ),
    trace (ρ * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ B)) = R.readout () ρ B

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0 0
  norm_num [rejected, realize] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change trace (partialTraceLeft (1 : TwoQubit) * 0) ≠
    trace (partialTraceLeft (1 : TwoQubit) * 1)
  rw [mul_zero, trace_zero, mul_one, trace_partialTraceLeft]
  norm_num [trace_one]

def source_registration : Registration arena (type_of% @trace_mul_one_kron) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨trace_mul_one_kron, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

end BobTrace

namespace CanonicalTrace

/-- Observe the full trace, retaining the canonical marginal hypothesis. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => TwoQubit) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ σ => trace σ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (σ : TwoQubit) (_hB : partialTraceLeft σ = (1 / 2 : ℂ) • 1),
    R.readout () () σ = 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hB : partialTraceLeft ((1 / 4 : ℂ) • (1 : TwoQubit)) = (1 / 2 : ℂ) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [partialTraceLeft, Fin.sum_univ_two, Matrix.one_apply]
  have he := h ((1 / 4 : ℂ) • (1 : TwoQubit)) hB
  norm_num [rejected, realize] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change trace (0 : TwoQubit) ≠ trace (1 : TwoQubit)
  norm_num [trace_one]

def source_registration : Registration arena (type_of% @canonical_trace) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨canonical_trace, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

end CanonicalTrace

namespace KroneckerDifference

/-- Observe the matrix difference in the left Kronecker product. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Matrix (Fin 2) (Fin 2) ℂ)
    (fun _ => Matrix (Fin 2) (Fin 2) ℂ) (fun _ => Matrix (Fin 2) (Fin 2) ℂ)

def actual : Realization signature :=
  realize signature (fun _ X Y => X - Y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ A X Y : Matrix (Fin 2) (Fin 2) ℂ,
    A ⊗ₖ R.readout () X Y = A ⊗ₖ X - A ⊗ₖ Y

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 1 1 0
  have hc := congrArg (fun Z : TwoQubit => Z (0, 0) (0, 0)) he
  norm_num [rejected, realize, kronecker_apply, Matrix.one_apply] at hc

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change (0 : Matrix (Fin 2) (Fin 2) ℂ) - 0 ≠ 0 - 1
  simp

def source_registration : Registration arena (type_of% @kron_sub) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨kron_sub, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

end KroneckerDifference

namespace CanonicalFilter

/-- Observe the determinant norm of the reverse Bob filter. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Matrix (Fin 2) (Fin 2) ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ F => Complex.normSq (det F)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (ρ : TwoQubit) (_hρ : ρ.PosSemidef) (_htr : trace ρ = 1)
      (_hb : vlen (blochB ρ) < 1),
    ∃ (σ : TwoQubit) (F : Matrix (Fin 2) (Fin 2) ℂ), σ.PosSemidef ∧
      partialTraceLeft σ = (1 / 2 : ℂ) • 1 ∧ blochA σ = centre ρ ∧
      ρ = ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ F) * σ *
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ F)ᴴ ∧
      F * Fᴴ = (2 : ℂ) • partialTraceLeft ρ ∧
      R.readout () () F = 1 - vlen (blochB ρ) ^ 2

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let ρ : TwoQubit := (1 / 4 : ℂ) • 1
  have hρ : ρ.PosSemidef := PosSemidef.one.smul (by norm_num [Complex.le_def])
  have htr : trace ρ = 1 := by norm_num [ρ, trace_smul, trace_one]
  have hb : blochB ρ = 0 := by
    funext i
    fin_cases i <;>
      norm_num [ρ, blochB, pauli, pauliMatrix, qubitX, qubitZ, Matrix.smul_mul,
        trace_smul, trace_kronecker, trace_fin_two]
  have hlen : vlen (blochB ρ) = 0 := by simp [hb, vlen]
  obtain ⟨σ, F, _, _, _, _, _, he⟩ := h ρ hρ htr (by rw [hlen]; norm_num)
  norm_num [rejected, realize, hlen] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change Complex.normSq (det (0 : Matrix (Fin 2) (Fin 2) ℂ)) ≠
    Complex.normSq (det (1 : Matrix (Fin 2) (Fin 2) ℂ))
  norm_num

def source_registration : Registration arena (type_of% @canonical_filter) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨canonical_filter, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

end CanonicalFilter

namespace AxisLength

/-- Observe the absolute scalar coordinate of the third-axis vector. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ s => |s|) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ s : ℝ, vlen ![0, 0, s] = R.readout () () s

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 1
  norm_num [rejected, realize, vlen_e3] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change |(0 : ℝ)| ≠ |(1 : ℝ)|
  norm_num

def source_registration : Registration arena (type_of% @vlen_e3) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨vlen_e3, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

end AxisLength

namespace VectorLength

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@vlen_eq_norm) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    (Lean.Name.str `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
      "VectorLength") "unit"
  realizationName := Lean.Name.str
    (Lean.Name.str `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
      "VectorLength") "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => vlen v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end VectorLength

namespace BlochVector

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@blochVec_eq_bloch) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    (Lean.Name.str `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
      "BlochVector") "unit"
  realizationName := Lean.Name.str
    (Lean.Name.str `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
      "BlochVector") "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ Z => blochVec Z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end BlochVector

namespace AliceTrace

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@trace_mul_kron_one) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    (Lean.Name.str `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
      "AliceTrace") "unit"
  realizationName := Lean.Name.str
    (Lean.Name.str `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
      "AliceTrace") "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ρ A => trace (partialTraceRight ρ * A))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end AliceTrace

namespace BobTrace

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@trace_mul_one_kron) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    (Lean.Name.str `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
      "BobTrace") "unit"
  realizationName := Lean.Name.str
    (Lean.Name.str `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
      "BobTrace") "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ρ B => trace (partialTraceLeft ρ * B))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end BobTrace

namespace CanonicalTrace

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@canonical_trace) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    (Lean.Name.str `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
      "CanonicalTrace") "unit"
  realizationName := Lean.Name.str
    (Lean.Name.str `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
      "CanonicalTrace") "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ σ => trace σ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end CanonicalTrace

namespace KroneckerDifference

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@kron_sub) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    (Lean.Name.str `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
      "KroneckerDifference") "unit"
  realizationName := Lean.Name.str
    (Lean.Name.str `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
      "KroneckerDifference") "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ X Y => X - Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end KroneckerDifference

namespace CanonicalFilter

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@canonical_filter) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    (Lean.Name.str `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
      "CanonicalFilter") "unit"
  realizationName := Lean.Name.str
    (Lean.Name.str `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
      "CanonicalFilter") "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ F => Complex.normSq (det F)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end CanonicalFilter

namespace AxisLength

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@vlen_e3) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    (Lean.Name.str `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
      "AxisLength") "unit"
  realizationName := Lean.Name.str
    (Lean.Name.str `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
      "AxisLength") "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => |s|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end AxisLength

end
end Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction

namespace Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
open _root_.D5.S3.QuantumBounds.CHSHWitness renaming TwoQubitMatrix → TwoQubit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped Kronecker

noncomputable section
namespace ConjugateKroneckerTrace

/-- Observe the trace paired with the conjugated Kronecker coefficient. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => TwoQubit) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ Z => trace Z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K A : Matrix (Fin 2) (Fin 2) ℂ) (ρ : TwoQubit),
    trace (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K) * ρ *
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K)ᴴ *
      (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))) =
        R.readout () () (ρ * (A ⊗ₖ (Kᴴ * K)))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0 0 0
  norm_num [rejected, realize] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change trace (0 : TwoQubit) ≠ trace (1 : TwoQubit)
  norm_num [trace_one]

def source_registration : Registration arena (type_of% @trace_conj_kron) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨trace_conj_kron, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@trace_conj_kron) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    (Lean.Name.str
      `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
      "ConjugateKroneckerTrace") "unit"
  realizationName := Lean.Name.str
    (Lean.Name.str
      `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
      "ConjugateKroneckerTrace") "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ Z => trace Z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end ConjugateKroneckerTrace
end
end Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction

namespace Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (pauli pauli_zero pauli_one pauli_two)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace PauliReadout

/-- Observe the Pauli matrix as its index varies. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 3)
    (fun _ => Matrix (Fin 2) (Fin 2) ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ i => pauli i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 2, ?_⟩
  change pauli 0 ≠ pauli 2
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) h
  norm_num [pauli_zero, pauli_two] at he

end PauliReadout

namespace PauliZero
abbrev arena : Arena where
  signature := PauliReadout.signature
  Law R := R.readout () () 0 = !![0, 1; 1, 0]

theorem rejected_law : ¬ arena.Law PauliReadout.rejected := by
  intro h
  change (0 : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; 1, 0] at h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 1).re) h
  norm_num [PauliReadout.rejected, realize, Matrix.zero_apply] at he

def source_registration : Registration arena (type_of% @pauli_zero) where
  actual := PauliReadout.actual
  bridge := Iff.rfl
  variation := ⟨pauli_zero, PauliReadout.rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    PauliReadout.actual PauliReadout.rejected rejected_law
  dependence := PauliReadout.dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli_zero)
      (Realization PauliReadout.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.PauliZero.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.PauliZero
    "source_registration"
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize PauliReadout.signature (fun _ _ i => pauli i) (fun e => nomatch e))
  variation := .absent, sensitivity := .absent
  partialSensitivity := none, escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0, functionOperand := false
      stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none, options := #[] }

#print axioms source_registration
#print axioms registration

end PauliZero

namespace PauliOne
abbrev arena : Arena where
  signature := PauliReadout.signature
  Law R := R.readout () () 1 = !![0, -Complex.I; Complex.I, 0]

theorem rejected_law : ¬ arena.Law PauliReadout.rejected := by
  intro h
  change (0 : Matrix (Fin 2) (Fin 2) ℂ) = !![0, -Complex.I; Complex.I, 0] at h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 1).im) h
  norm_num [PauliReadout.rejected, realize, Matrix.zero_apply] at he

def source_registration : Registration arena (type_of% @pauli_one) where
  actual := PauliReadout.actual
  bridge := Iff.rfl
  variation := ⟨pauli_one, PauliReadout.rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    PauliReadout.actual PauliReadout.rejected rejected_law
  dependence := PauliReadout.dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli_one)
      (Realization PauliReadout.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.PauliOne.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.PauliOne
    "source_registration"
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize PauliReadout.signature (fun _ _ i => pauli i) (fun e => nomatch e))
  variation := .absent, sensitivity := .absent
  partialSensitivity := none, escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0, functionOperand := false
      stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none, options := #[] }

#print axioms source_registration
#print axioms registration

end PauliOne

namespace PauliTwo
abbrev arena : Arena where
  signature := PauliReadout.signature
  Law R := R.readout () () 2 = !![1, 0; 0, -1]

theorem rejected_law : ¬ arena.Law PauliReadout.rejected := by
  intro h
  change (0 : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; 0, -1] at h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) h
  norm_num [PauliReadout.rejected, realize, Matrix.zero_apply] at he

def source_registration : Registration arena (type_of% @pauli_two) where
  actual := PauliReadout.actual
  bridge := Iff.rfl
  variation := ⟨pauli_two, PauliReadout.rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    PauliReadout.actual PauliReadout.rejected rejected_law
  dependence := PauliReadout.dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli_two)
      (Realization PauliReadout.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.PauliTwo.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.PauliTwo
    "source_registration"
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize PauliReadout.signature (fun _ _ i => pauli i) (fun e => nomatch e))
  variation := .absent, sensitivity := .absent
  partialSensitivity := none, escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0, functionOperand := false
      stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none, options := #[] }

#print axioms source_registration
#print axioms registration

end PauliTwo
end
end Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction

namespace Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (vlen vlen_e3 vlen_nonneg)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace VectorLengthNonnegative

/-- Observe the Euclidean length of a real three-vector. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 3 → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ v => vlen v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ v : Fin 3 → ℝ, 0 ≤ R.readout () () v

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0
  change (0 : ℝ) ≤ -1 at he
  linarith

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, ![0, 0, 1], ?_⟩
  change vlen (0 : Fin 3 → ℝ) ≠ vlen ![0, 0, 1]
  rw [vlen_e3]
  norm_num [vlen]

def source_registration : Registration arena (type_of% @vlen_nonneg) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨vlen_nonneg, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.vlen_nonneg)
      (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.VectorLengthNonnegative
    "unit"
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.VectorLengthNonnegative
    "source_registration"
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => vlen v) (fun e => nomatch e))
  variation := .absent, sensitivity := .absent
  partialSensitivity := none, escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "fn"]
      stateBinder := 0, functionOperand := true
      stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none, options := #[] }

#print axioms source_registration
#print axioms registration

end VectorLengthNonnegative
end
end Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
