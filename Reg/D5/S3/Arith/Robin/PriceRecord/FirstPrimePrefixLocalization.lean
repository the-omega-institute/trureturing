import D5.S3.Arith.Robin.PriceRecord.FirstPrimePrefixLocalization
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.Robin.PriceRecord.FirstPrimePrefixLocalization

open Real Finset Filter
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open _root_.Reg.D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity
open _root_.D5.S3.Arith.Robin.PriceRecord.FirstPrimePrefixLocalization
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Topology

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => log z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem log_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, exp 1, ?_⟩
  change log 1 ≠ log (exp 1)
  simp

namespace Windows

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A : ℕ) {e : ℝ}, 0 < e → e ≤ 1 / 4 →
    ∀ᶠ z : ℝ in atTop,
      1 < z ∧ 1 ≤ R.readout () () z ∧
      0 < e / log z ^ A ∧ e / log z ^ A ≤ 1 / 4 ∧
      4 ≤ (e / log z ^ A) * z ∧
      (e / log z ^ A) * z / 8 ≤
        Chebyshev.theta (z * (1 - (e / log z ^ A) / 2)) -
          Chebyshev.theta (z * (1 - 3 * (e / log z ^ A) / 4)) ∧
      (e / log z ^ A) * z / 8 ≤
        Chebyshev.theta (z * (1 + 3 * (e / log z ^ A) / 4)) -
          Chebyshev.theta (z * (1 + (e / log z ^ A) / 2))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨z, hz⟩ := (h 0 (e := 1 / 4) (by norm_num) le_rfl).exists
  have hb := hz.2.1
  change (1 : ℝ) ≤ 0 at hb
  norm_num at hb

def family : Registration arena (type_of% (@eventually_first_prefix_windows)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨eventually_first_prefix_windows, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := log_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eventually_first_prefix_windows) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.FirstPrimePrefixLocalization.eventually_first_prefix_windows.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.FirstPrimePrefixLocalization.Windows.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => log z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.FirstPrimePrefixLocalization
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "body", "body", "fn", "arg", "body", "arg", "fn", "arg", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Windows

namespace Localization

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A : ℕ) {K : ℝ}, 0 ≤ K → ∀ {ε : ℝ}, 0 < ε →
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z : ℝ, Z ≤ z → ∀ n : ℕ, 1 ≤ n →
      n.primeFactors = Nat.primesLE (largestPrime n) →
      sqrt z * R.readout () () z * actualDefect z n ≤ K →
      |log z ^ A * ((largestPrime n : ℝ) / z - 1)| < ε

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨Z, hZ, hz⟩ := h 0 (K := 0) le_rfl (ε := 1) (by norm_num)
  have hsupport : (1 : ℕ).primeFactors = Nat.primesLE (largestPrime 1) := by
    norm_num [_root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail.largestPrime]
  have hbudget : sqrt Z * rejected.readout () () Z * actualDefect Z 1 ≤ 0 := by
    change sqrt Z * 0 * actualDefect Z 1 ≤ 0
    simp
  have hb := hz Z le_rfl 1 le_rfl hsupport hbudget
  norm_num [rejected, realize,
    _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail.largestPrime] at hb

def family : Registration arena (type_of% (@bounded_defect_first_prefix_localization)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bounded_defect_first_prefix_localization, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := log_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bounded_defect_first_prefix_localization) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.FirstPrimePrefixLocalization.bounded_defect_first_prefix_localization.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.FirstPrimePrefixLocalization.Localization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => log z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.FirstPrimePrefixLocalization
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "domain", "fn", "arg", "fn", "arg", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Localization

namespace FirstCharge

abbrev arena : Arena where
  signature := DefectObservation.signature
  Law R := ∀ {z : ℝ}, 1 < z → ∀ {n : ℕ}, 1 ≤ n →
    ∀ (H X : Finset ℕ), Disjoint H X → ∀ {ρ : ℝ}, 0 ≤ ρ →
    (∀ p ∈ H, p.Prime ∧ n.factorization p = 0 ∧
      ρ ≤ goldenLayerMarginal p 1 - referencePrice z) →
    (∀ p ∈ X, p.Prime ∧ 1 ≤ n.factorization p ∧
      ρ ≤ referencePrice z - goldenLayerMarginal p 1) →
    ρ * ((∑ p ∈ H, log p) + ∑ p ∈ X, log p) ≤ R.readout () z n

private theorem rejected_law : ¬ arena.Law DefectObservation.rejected := by
  intro h
  have hb := h (z := 2) (by norm_num) (n := 1) le_rfl ∅ ∅ (by simp)
    (ρ := 0) le_rfl (by simp) (by simp)
  norm_num [DefectObservation.rejected, realize] at hb

def family : Registration arena (type_of% (@actual_first_layer_charge)) where
  actual := DefectObservation.actual
  bridge := Iff.rfl
  variation := ⟨actual_first_layer_charge, DefectObservation.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨DefectObservation.rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := DefectObservation.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_first_layer_charge) (Realization DefectObservation.signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.FirstPrimePrefixLocalization.actual_first_layer_charge.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.FirstPrimePrefixLocalization.FirstCharge.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize DefectObservation.signature
    (fun _ z n => actualDefect z n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.FirstPrimePrefixLocalization
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end FirstCharge

namespace Displacement

abbrev arena : Arena where
  signature := DefectObservation.signature
  Law R := ∀ {z η : ℝ}, 1 < z → 0 < η → η ≤ 1 / 4 → 4 ≤ η * z →
    (η * z / 8 ≤ Chebyshev.theta (z * (1 - η / 2)) -
      Chebyshev.theta (z * (1 - 3 * η / 4))) →
    (η * z / 8 ≤ Chebyshev.theta (z * (1 + 3 * η / 4)) -
      Chebyshev.theta (z * (1 + η / 2))) →
    ∀ {n : ℕ}, 1 ≤ n → n.primeFactors = Nat.primesLE (largestPrime n) →
    ((largestPrime n : ℝ) ≤ z * (1 - η) ∨ z * (1 + η) ≤ (largestPrime n : ℝ)) →
    η ^ 2 * sqrt z / 32 ≤ sqrt z * log z * R.readout () z n

private theorem rejected_law : ¬ arena.Law DefectObservation.rejected := by
  intro h
  have hev := eventually_first_prefix_windows 0 (e := 1 / 4) (by norm_num) le_rfl
  obtain ⟨z, hz⟩ := hev.exists
  simp only [pow_zero, div_one] at hz
  obtain ⟨hz1, hL, hη, hηb, hsize, hbelow, habove⟩ := hz
  have hsupport : (1 : ℕ).primeFactors = Nat.primesLE (largestPrime 1) := by
    norm_num [_root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail.largestPrime]
  have hfar : (largestPrime 1 : ℝ) ≤ z * (1 - (1 / 4 : ℝ)) ∨
      z * (1 + (1 / 4 : ℝ)) ≤ (largestPrime 1 : ℝ) := by
    left
    norm_num [_root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail.largestPrime]
    linarith
  have hb := h hz1 hη hηb hsize hbelow habove le_rfl hsupport hfar
  change (1 / 4 : ℝ) ^ 2 * sqrt z / 32 ≤ sqrt z * log z * (-1) at hb
  have hs : 0 < sqrt z := sqrt_pos.mpr (by linarith)
  have hp : 0 < sqrt z * log z := mul_pos hs (log_pos hz1)
  nlinarith

def family : Registration arena (type_of% (@first_prefix_displacement_charge)) where
  actual := DefectObservation.actual
  bridge := Iff.rfl
  variation := ⟨first_prefix_displacement_charge, DefectObservation.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨DefectObservation.rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := DefectObservation.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@first_prefix_displacement_charge) (Realization DefectObservation.signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.FirstPrimePrefixLocalization.first_prefix_displacement_charge.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.FirstPrimePrefixLocalization.Displacement.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize DefectObservation.signature
    (fun _ z n => actualDefect z n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.FirstPrimePrefixLocalization
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Displacement

end Reg.D5.S3.Arith.Robin.PriceRecord.FirstPrimePrefixLocalization
