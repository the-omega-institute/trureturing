import D5.S3.Arith.CMJet.Integral
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The integral jet readout allows all derivative orders and integral polynomial pairs. -/

noncomputable section

namespace Reg.D5.S3.Arith.CMJet.Integral

open LeanInformationAudit
open _root_.D5.S3.Arith.CMJet
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)

abbrev readoutSignature : Signature :=
  signature (Σ _ : ℕ, ℕ) (fun _ => Curve ℤ) (fun _ => ℤ)

def actual : Realization readoutSignature :=
  realize readoutSignature (fun _ pn z => atO (iter pn.2 z)) (fun e => nomatch e)

def rejected : Realization readoutSignature :=
  realize readoutSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := readoutSignature
  Law R := ∀ {p : ℕ} [Fact p.Prime], p % 4 = 3 → ∀ (N : ℕ) (z : Curve ℤ),
    (p : ℤ) ^ (N / p) ∣ R.readout () ⟨p, N⟩ z

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbad := h (p := 3) (by decide) 3 0
  norm_num [rejected, realize] at hbad

def family : Registration arena (type_of% @inert_dvd_jet) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@inert_dvd_jet, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨⟨3, 0⟩, 0, 1, ?_⟩
    simp [actual, realize, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
      Polynomial.coeff_one_zero]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@inert_dvd_jet) (Realization readoutSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.CMJet.Integral.unit
  realizationName := `Reg.D5.S3.Arith.CMJet.Integral.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize readoutSignature (fun _ pn z => atO (iter pn.2 z)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.CMJet.Integral
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

open scoped Function

namespace Iteration

abbrev readoutSignature : Signature :=
  signature ℕ (fun _ => Curve ℤ) (fun _ => Curve ℤ)

def actual : Realization readoutSignature :=
  realize readoutSignature (fun _ N z => iter N z) (fun e => nomatch e)

def rejected : Realization readoutSignature :=
  realize readoutSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := readoutSignature
  Law R := ∀ {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) (N : ℕ) (z : Curve ℤ),
    R.readout () N z = (p : ℤ) ^ (N / p) • (inertLift hp)^[N / p] (iter (N % p) z)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbad : (1 : Curve ℤ) = 0 := by simpa [rejected, realize] using h (p := 3) (by decide) 0 0
  exact one_ne_zero hbad

def family : Registration arena (type_of% @iter_eq_inertLift) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@iter_eq_inertLift, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨0, 0, 1, ?_⟩
    simpa [actual, realize] using (zero_ne_one : (0 : Curve ℤ) ≠ 1)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@iter_eq_inertLift) (Realization readoutSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.CMJet.Integral.Iteration.unit
  realizationName := `Reg.D5.S3.Arith.CMJet.Integral.Iteration.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize readoutSignature (fun _ N z => iter N z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.CMJet.Integral
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Iteration

namespace LastColumn

abbrev readoutSignature : Signature :=
  signature Unit (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization readoutSignature :=
  realize readoutSignature (fun _ _ m => row m (Fin.last m)) (fun e => nomatch e)

def rejected : Realization readoutSignature :=
  realize readoutSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := readoutSignature
  Law R := ∀ m : ℕ, R.readout () () m = ↑(order m).factorial

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 0
  norm_num [rejected, realize, order] at hbad

def family : Registration arena (type_of% @row_last) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@row_last, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    change ∃ (_ : Unit) (l r : ℕ), row l (Fin.last l) ≠ row r (Fin.last r)
    refine ⟨(), 0, 1, ?_⟩
    rw [row_last, row_last]
    norm_num [order, Nat.factorial_succ]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@row_last) (Realization readoutSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.CMJet.Integral.LastColumn.unit
  realizationName := `Reg.D5.S3.Arith.CMJet.Integral.LastColumn.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize readoutSignature (fun _ _ m => row m (Fin.last m)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.CMJet.Integral
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
  options := #[]

end LastColumn

end Reg.D5.S3.Arith.CMJet.Integral
