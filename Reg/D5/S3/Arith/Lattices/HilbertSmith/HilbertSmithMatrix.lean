import D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix

open _root_.D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix
open _root_.D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula
open _root_.D5.S3.Arith.Lattices.HilbertSmith.MinorValuation
open _root_.D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset
open scoped BigOperators

noncomputable section

private theorem intervalOne : intervalLCM 1 1 = 1 := by decide

private theorem scaleTwo : intervalLCM 1 1 ∣ 2 := by
  simpa only [intervalOne] using (one_dvd (2 : ℕ))

private theorem divisorOneTwo : determinantalDivisor 1 2 1 = 2 := by
  rw [determinantalDivisor_succ (k := 0) (by decide) scaleTwo (by decide),
    determinantalDivisor_zero, intervalOne, one_mul, Nat.div_one]

private theorem factorOneTwo :
    determinantalDivisor 1 2 1 / determinantalDivisor 1 2 (1 - 1) = 2 := by
  rw [smithFactor_eq_intervalLCM (by decide) scaleTwo (by decide) (by decide),
    intervalOne, Nat.div_one]

abbrev natSignature (P : Type) : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature P (fun _ => ℕ) (fun _ => ℕ)

namespace MinorDeterminant

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, Finset ℕ)
    (fun _ => Finset ℕ) (fun _ => ℚ)

def actual : Realization signature :=
  realize signature (fun _ p J => cauchyMinor p.1 p.2 J) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n k L : ℕ} (hd : intervalLCM n 1 ∣ L)
      {I J : Finset ℕ} (hI : I ⊆ range n) (hJ : J ⊆ range n)
      (hIk : I.card = k) (hJk : J.card = k),
      ((integerHilbertMinor L hI hJ hIk hJk).det : ℚ) = R.readout () ⟨L, I⟩ J

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hsubset : (∅ : Finset ℕ) ⊆ range 1 := empty_subset _
  have hcard : (∅ : Finset ℕ).card = 0 := card_empty
  have hbad := h (L := 2) scaleTwo hsubset hsubset hcard hcard
  rw [det_integerHilbertMinor_cast scaleTwo hsubset hsubset hcard hcard] at hbad
  exact (cauchyMinor_pos (by decide : 0 < (2 : ℕ)) ∅ ∅).ne' hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨1, {0}⟩, {0}, {1}, ?_⟩
  change cauchyMinor 1 {0} {0} ≠ cauchyMinor 1 {0} {1}
  norm_num [cauchyMinor, positiveDifferences, denominatorProduct, Finset.prod_product]

def family : Registration arena (type_of% @det_integerHilbertMinor_cast) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@det_integerHilbertMinor_cast, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@det_integerHilbertMinor_cast) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix.det_integerHilbertMinor_cast.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix.MinorDeterminant.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p J => cauchyMinor p.1 p.2 J) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix
    definition := none
    coordinates := #[2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MinorDeterminant

namespace MinorValuation

abbrev signature : Signature :=
  natSignature ℕ

def actual : Realization signature :=
  realize signature (fun _ p L => L.factorization p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p n L k : ℕ} (hp : p.Prime) (hL : 0 < L)
      (hd : intervalLCM n 1 ∣ L) {I J : Finset ℕ}
      (hI : I ⊆ range n) (hJ : J ⊆ range n) (hIk : I.card = k) (hJk : J.card = k),
      2 * (integerHilbertMinorAbs L hI hJ hIk hJk).factorization p =
        2 * k * (R.readout () p L - Nat.log p (2 * n - 1)) +
          ∑ a ∈ Icc 1 (Nat.log p (2 * n - 1)), residueLoss (p ^ a) I J

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hclear : intervalLCM 1 1 ∣ 1 := by
    simpa only [intervalOne] using (one_dvd (1 : ℕ))
  have hsubset : range 1 ⊆ range 1 := Subset.rfl
  have hcard : (range 1).card = 1 := card_range 1
  have hbad := h (p := 2) (L := 1) Nat.prime_two (by decide) hclear
    hsubset hsubset hcard hcard
  rw [integerHilbertMinor_valuation Nat.prime_two (by decide) hclear
    hsubset hsubset hcard hcard] at hbad
  have he : Icc (1 : ℕ) 0 = ∅ := Icc_eq_empty_of_lt (by decide)
  norm_num [rejected, realize, Nat.factorization_one, Nat.log_one_right, he] at hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨2, 1, 2, ?_⟩
  change (1 : ℕ).factorization 2 ≠ (2 : ℕ).factorization 2
  rw [Nat.factorization_one, Nat.prime_two.factorization_self]
  decide

def family : Registration arena (type_of% @integerHilbertMinor_valuation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integerHilbertMinor_valuation, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integerHilbertMinor_valuation) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix.integerHilbertMinor_valuation.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix.MinorValuation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p L => L.factorization p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "fn", "arg",
        "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MinorValuation

namespace EmptyDivisor

abbrev signature : Signature :=
  natSignature (Σ _ : ℕ, ℕ)

def actual : Realization signature :=
  realize signature (fun _ p k => determinantalDivisor p.1 p.2 k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n L : ℕ), R.readout () ⟨n, L⟩ 0 = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (by decide : (0 : ℕ) ≠ 1) (h 0 0)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨1, 2⟩, 0, 1, ?_⟩
  change determinantalDivisor 1 2 0 ≠ determinantalDivisor 1 2 1
  rw [determinantalDivisor_zero, divisorOneTwo]
  decide

def family : Registration arena (type_of% @determinantalDivisor_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@determinantalDivisor_zero, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@determinantalDivisor_zero) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix.determinantalDivisor_zero.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix.EmptyDivisor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => determinantalDivisor p.1 p.2 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end EmptyDivisor

namespace NonzeroDivisor

abbrev signature : Signature :=
  natSignature (Σ _ : ℕ, ℕ)

def actual : Realization signature :=
  realize signature (fun _ p k => determinantalDivisor p.1 p.2 k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n k L : ℕ} (hk : k ≤ n) (hL : 0 < L)
      (hd : intervalLCM n 1 ∣ L), R.readout () ⟨n, L⟩ k ≠ 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (k := 0) (by decide) (by decide) scaleTwo rfl

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨1, 2⟩, 0, 1, ?_⟩
  change determinantalDivisor 1 2 0 ≠ determinantalDivisor 1 2 1
  rw [determinantalDivisor_zero, divisorOneTwo]
  decide

def family : Registration arena (type_of% @determinantalDivisor_ne_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@determinantalDivisor_ne_zero, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@determinantalDivisor_ne_zero) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix.determinantalDivisor_ne_zero.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix.NonzeroDivisor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => determinantalDivisor p.1 p.2 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end NonzeroDivisor

namespace DivisorValuation

abbrev signature : Signature :=
  natSignature (Σ _ : ℕ, Σ _ : ℕ, ℕ)

def actual : Realization signature :=
  realize signature (fun _ p k => divisorExponent p.1 p.2.1 p.2.2 k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p n L k : ℕ} (hp : p.Prime) (hL : 0 < L)
      (hd : intervalLCM n 1 ∣ L) (hk : k ≤ n),
      (determinantalDivisor n L k).factorization p = R.readout () ⟨p, n, L⟩ k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h Nat.prime_two (by decide) scaleTwo (by decide : 1 ≤ (1 : ℕ))
  rw [divisorOneTwo, Nat.prime_two.factorization_self] at hbad
  exact (by decide : (1 : ℕ) ≠ 0) hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨2, 1, 2⟩, 0, 1, ?_⟩
  change divisorExponent 2 1 2 0 ≠ divisorExponent 2 1 2 1
  have he : Icc (1 : ℕ) 0 = ∅ := Icc_eq_empty_of_lt (by decide)
  norm_num [divisorExponent, Nat.prime_two.factorization_self, Nat.log_one_right, he]

def family : Registration arena (type_of% @determinantalDivisor_factorization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@determinantalDivisor_factorization, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@determinantalDivisor_factorization) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix.determinantalDivisor_factorization.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix.DivisorValuation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => divisorExponent p.1 p.2.1 p.2.2 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DivisorValuation

namespace DivisorRecurrence

abbrev signature : Signature :=
  natSignature (Σ _ : ℕ, ℕ)

def actual : Realization signature :=
  realize signature (fun _ p k => p.2 / intervalLCM p.1 k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n L k : ℕ} (hL : 0 < L)
      (hd : intervalLCM n 1 ∣ L) (hk : k + 1 ≤ n),
      determinantalDivisor n L (k + 1) =
        determinantalDivisor n L k * R.readout () ⟨n, L⟩ (k + 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (k := 0) (by decide) scaleTwo (by decide)
  change determinantalDivisor 1 2 1 = determinantalDivisor 1 2 0 * 0 at hbad
  rw [divisorOneTwo, mul_zero] at hbad
  exact (by decide : (2 : ℕ) ≠ 0) hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨2, 6⟩, 1, 2, ?_⟩
  change 6 / intervalLCM 2 1 ≠ 6 / intervalLCM 2 2
  decide

def family : Registration arena (type_of% @determinantalDivisor_succ) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@determinantalDivisor_succ, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@determinantalDivisor_succ) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix.determinantalDivisor_succ.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix.DivisorRecurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => p.2 / intervalLCM p.1 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DivisorRecurrence

namespace FactorFormula

abbrev signature : Signature :=
  natSignature (Σ _ : ℕ, ℕ)

def actual : Realization signature :=
  realize signature (fun _ p k => p.2 / intervalLCM p.1 k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n L k : ℕ} (hL : 0 < L)
      (hd : intervalLCM n 1 ∣ L) (hk : 0 < k) (hkn : k ≤ n),
      determinantalDivisor n L k / determinantalDivisor n L (k - 1) =
        R.readout () ⟨n, L⟩ k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (k := 1) (by decide) scaleTwo (by decide) (by decide)
  rw [factorOneTwo] at hbad
  exact (by decide : (2 : ℕ) ≠ 0) hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨2, 6⟩, 1, 2, ?_⟩
  change 6 / intervalLCM 2 1 ≠ 6 / intervalLCM 2 2
  decide

def family : Registration arena (type_of% @smithFactor_eq_intervalLCM) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@smithFactor_eq_intervalLCM, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@smithFactor_eq_intervalLCM) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix.smithFactor_eq_intervalLCM.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix.FactorFormula.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => p.2 / intervalLCM p.1 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FactorFormula

namespace FactorChain

abbrev signature : Signature :=
  natSignature (Σ _ : ℕ, ℕ)

def actual : Realization signature :=
  realize signature (fun _ p k => determinantalDivisor p.1 p.2 k / determinantalDivisor p.1 p.2 (k - 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n L k l : ℕ} (hL : 0 < L)
      (hd : intervalLCM n 1 ∣ L) (hk : 0 < k) (hkl : k ≤ l) (hln : l ≤ n),
      0 < R.readout () ⟨n, L⟩ k ∧
      (determinantalDivisor n L k / determinantalDivisor n L (k - 1)) ∣
        (determinantalDivisor n L l / determinantalDivisor n L (l - 1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (by decide : ¬ 0 < (0 : ℕ))
    (h (k := 1) (l := 1) (by decide) scaleTwo (by decide) (by decide) (by decide)).1

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨1, 2⟩, 0, 1, ?_⟩
  change determinantalDivisor 1 2 0 / determinantalDivisor 1 2 (0 - 1) ≠
    determinantalDivisor 1 2 1 / determinantalDivisor 1 2 (1 - 1)
  rw [factorOneTwo]
  change determinantalDivisor 1 2 0 / determinantalDivisor 1 2 0 ≠ 2
  rw [determinantalDivisor_zero]
  decide

def family : Registration arena (type_of% @smithFactor_pos_and_dvd) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@smithFactor_pos_and_dvd, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@smithFactor_pos_and_dvd) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix.smithFactor_pos_and_dvd.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix.FactorChain.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => determinantalDivisor p.1 p.2 k / determinantalDivisor p.1 p.2 (k - 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FactorChain

namespace Minimizer

open _root_.D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix
open _root_.D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula
open _root_.D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ n q => commonCapacity n q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨1, 1, 2, ?_⟩
  change commonCapacity 1 1 ≠ commonCapacity 1 2
  decide

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p n L k : ℕ}, p.Prime → 0 < L → intervalLCM n 1 ∣ L → k ≤ n →
    ∃ (I J : Finset ℕ) (hI : I ⊆ range n) (hJ : J ⊆ range n)
      (hIk : I.card = k) (hJk : J.card = k),
      (integerHilbertMinorAbs L hI hJ hIk hJk).factorization p =
        divisorExponent p n L k ∧
      ∀ a ≤ Nat.log p (2 * n - 1),
        residueLoss (p ^ a) I J = 2 * (k - R.readout () n (p ^ a))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨I, J, hI, hJ, hIk, hJk, _, hbad⟩ :=
    h (p := 2) (n := 1) (L := 1) (k := 1)
      (by decide) (by decide) (by decide) (by decide)
  have hi : I = range 1 := eq_of_subset_of_card_le hI (by simpa [hIk])
  have hj : J = range 1 := eq_of_subset_of_card_le hJ (by simpa [hJk])
  subst I
  subst J
  exact (by decide : residueLoss 1 (range 1) (range 1) ≠ 2 * (1 - 0))
    (hbad 0 (Nat.zero_le _))

def family : Registration arena (type_of% @exists_integerHilbertMinor_minimizer) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_integerHilbertMinor_minimizer, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_integerHilbertMinor_minimizer) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix.exists_integerHilbertMinor_minimizer.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix.Minimizer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n q => commonCapacity n q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "body",
        "arg", "body", "arg", "body", "arg", "body",
        "arg", "body", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Minimizer

end

end Reg.D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix
