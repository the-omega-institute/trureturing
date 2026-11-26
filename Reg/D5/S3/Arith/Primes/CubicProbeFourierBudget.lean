import D5.S3.Arith.Primes.CubicProbeFourierBudget
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.Arith.Primes.CubicProbeFourierBudget
open _root_.D5.S3.Arith.Primes.CubicProbeFourierBudget
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
set_option autoImplicit false
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Finset Nat)
    (fun _ => Finset Nat) (fun _ => Rat)

/-- The selected observation is the actual normalized Fourier charge,
with the split observation set retained as a parameter. -/
def actual : Realization signature :=
  realize signature (fun _ A B => fourierCharge A.card B.card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ A B => (3 : Rat)^A.card*(3 : Rat)^B.card) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P M : Nat) (_hP : 0<P),
    (∃ A B : Finset Nat,
        (∀ a∈A, a≤P) ∧ (∀ b∈B, b≤P) ∧ Disjoint A B ∧
        R.readout () A B ≤ (M : Rat) ∧ Force A B P) ↔
    ∃ a b : Nat, P-P/2≤a*b ∧ 3^a*2^b≤M

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hrhs : ∃ a b : Nat, 1-1/2 ≤ a*b ∧ 3^a*2^b≤6 :=
    ⟨1,1,by decide,by decide⟩
  obtain ⟨A,B,_,_,_,hc,hF⟩ := (h 1 6 (by decide)).mpr hrhs
  have ha : 0 < A.card := by
    by_contra hh
    have hz : A = ∅ := Finset.card_eq_zero.mp (by omega)
    have hf := hF (fun _ => false) (fun i hi => by simp [hz] at hi)
      (fun _ _ => rfl) 1 (by decide) (fun _ => rfl)
    omega
  have hb : 0 < B.card := by
    by_contra hh
    have hz : B = ∅ := Finset.card_eq_zero.mp (by omega)
    have hf := hF (fun _ => true) (fun _ _ => rfl)
      (fun i hi => by simp [hz] at hi) 1 (by decide) (fun _ => rfl)
    omega
  have hA : 3^1 ≤ 3^A.card := Nat.pow_le_pow_right (by decide) ha
  have hB : 3^1 ≤ 3^B.card := Nat.pow_le_pow_right (by decide) hb
  have hn : 9≤3^A.card*3^B.card := Nat.mul_le_mul hA hB
  have hq : (9 : Rat) ≤ (3 : Rat)^A.card*(3 : Rat)^B.card := by exact_mod_cast hn
  change (3 : Rat)^A.card*(3 : Rat)^B.card ≤ (6 : Rat) at hc
  have hbad := hq.trans hc
  norm_num at hbad

private theorem actual_dependence :
    actual.readout () {0} {2} ≠ actual.readout () {0} {1,2} := by decide +kernel

def family : Registration arena (type_of% @cubic_fourier_budget_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cubic_fourier_budget_iff,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨{0},{2},{1,2},actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@cubic_fourier_budget_iff) (type_of% actual) Unit Unit where
  unitName := `D5.S3.Arith.Primes.CubicProbeFourierBudget.cubic_fourier_budget_iff.__information_unit
  realizationName := `Reg.D5.S3.Arith.Primes.CubicProbeFourierBudget.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Primes.CubicProbeFourierBudget
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body","body","body","fn","arg","arg","body","arg","body","arg","arg","arg","fn","arg","fn","arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.Arith.Primes.CubicProbeFourierBudget
