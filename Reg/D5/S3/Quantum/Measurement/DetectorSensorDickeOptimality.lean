import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for the public theorems in the mirrored owner. -/

set_option linter.style.longLine false

set_option pp.proofs false in
#print D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.weight_class_card

namespace Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality

open _root_.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the binomial count at the selected weight. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ n k => n.choose k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ n k => n.choose k + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n k : ℕ,
    (Finset.univ.filter (fun x : Fin n → Bool =>
      (Finset.univ.filter (fun j => x j = true)).card = k)).card = R.readout () n k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 0
  change _ = Nat.choose 0 0 + 1 at hb
  rw [weight_class_card] at hb
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 2, ?_⟩
  change Nat.choose 1 0 ≠ Nat.choose 1 2
  norm_num

def source_registration : Registration arena (type_of% @weight_class_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weight_class_card, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@weight_class_card) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.weight_class_card.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => n.choose k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
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
  options := #[]

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality

namespace Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.CauchySchwarz
open _root_.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped MatrixOrder ComplexOrder
noncomputable section
universe u
/-- Read the real quadratic value appearing in the first diagonal factor. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => z.re) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {h : Type u} [Fintype h] [DecidableEq h]
    (H : Matrix h h ℂ) (_hH : H.PosSemidef) (x y : h → ℂ),
    ‖star x ⬝ᵥ (H *ᵥ y)‖ ^ 2 ≤
      R.readout () () (star x ⬝ᵥ (H *ᵥ x)) * (star y ⬝ᵥ (H *ᵥ y)).re
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (h := ULift.{u} Unit) 1 Matrix.PosSemidef.one
    (fun _ => 1) (fun _ => 1)
  change ‖star (fun _ : ULift.{u} Unit => (1 : ℂ)) ⬝ᵥ
    ((1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) *ᵥ (fun _ => 1))‖ ^ 2 ≤
      (-1 : ℝ) * (star (fun _ : ULift.{u} Unit => (1 : ℂ)) ⬝ᵥ
        ((1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) *ᵥ (fun _ => 1))).re at hh
  norm_num [dotProduct] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @psd_cauchy_schwarz) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@psd_cauchy_schwarz, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@psd_cauchy_schwarz) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.CauchySchwarz.unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.CauchySchwarz.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

set_option pp.proofs false in
#print psd_cauchy_schwarz
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.CauchySchwarz

namespace Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.GramDiagonal

open _root_.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.ProductPrefixRigidity
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Read the selected diagonal entry of the source Gram matrix. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ n : ℕ, Fin n)
    (fun p => Matrix (Fin p.1) (Fin p.1) ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ p M => M p.2 p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (θ : ℝ) (ψ : (Fin n → Bool) → ℂ)
    (_hψ : ∑ x, Complex.normSq (ψ x) = 1) (i : Fin n),
    R.readout () ⟨n, i⟩ (gram ((fun i => fire θ i ψ)ᵀ)) = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  have hb := h (n := 1) 0
    (fun x => if x = (fun _ => false) then 1 else 0) (by simp) 0
  change (0 : ℂ) = 1 at hb
  exact zero_ne_one hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
  change (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 ≠ 1
  simp

def source_registration : Registration arena (type_of% @G_diag) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@G_diag, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@G_diag) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.GramDiagonal.unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.GramDiagonal.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p M => M p.2 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

set_option pp.proofs false in
#print G_diag
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.GramDiagonal

namespace Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.CountsPartition

open _root_.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Read the binomial count in the partition identity. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ n k => n.choose k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ n k => n.choose k + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (i j : Fin n) (k : ℕ),
    rCount n i j k + lCount n i j k = R.readout () n k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1 0 0 0
  change _ = Nat.choose 1 0 + 1 at hb
  rw [counts_partition] at hb
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 2, ?_⟩
  change Nat.choose 1 0 ≠ Nat.choose 1 2
  norm_num

def source_registration : Registration arena (type_of% @counts_partition) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨counts_partition, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@counts_partition) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.CountsPartition.unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.CountsPartition.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => n.choose k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

set_option pp.proofs false in
#print counts_partition
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.CountsPartition

namespace Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.PairCountProduct

open _root_.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Read the binomial factor in the pair-count product. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ n k => n.choose k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ n k => n.choose k + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (a b : Fin n) (_hab : a ≠ b) (k : ℕ),
    lCount n a b k * (n * (n - 1)) = 2 * k * (n - k) * R.readout () n k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 2 0 1 (by decide) 1
  have ha := pair_count_product 2 0 1 (by decide) 1
  change lCount 2 0 1 1 * (2 * (2 - 1)) =
    2 * 1 * (2 - 1) * (Nat.choose 2 1 + 1) at hb
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 2, ?_⟩
  change Nat.choose 1 0 ≠ Nat.choose 1 2
  norm_num

def source_registration : Registration arena (type_of% @pair_count_product) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pair_count_product, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@pair_count_product) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.PairCountProduct.unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.PairCountProduct.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => n.choose k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

set_option pp.proofs false in
#print pair_count_product
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.PairCountProduct

namespace Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.DickeNormalized

open _root_.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Read the squared amplitude at the source sum's selected configuration. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => Complex.normSq z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (l : ℕ) (_hl : l ≤ n) (φ : (Fin n → Bool) → ℂ)
    (_hφ : ∀ x, Complex.normSq (φ x) =
      if (Finset.univ.filter (fun j => x j = true)).card = l
        then 1 / (n.choose l : ℝ) else 0),
    ∑ x, R.readout () () (φ x) = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (n := 0) 0 (by omega) (fun _ => 1) (by simp)
  simp [rejected, realize] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @dicke_normalized) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@dicke_normalized, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@dicke_normalized) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.DickeNormalized.unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.DickeNormalized.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => Complex.normSq z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

set_option pp.proofs false in
#print dicke_normalized
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.DickeNormalized
