import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.DirichletFiniteZeroFree
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex
open _root_.D5.S3.CharacterSums.DirichletZeroPowerSums
open _root_.D5.S3.CharacterSums.DirichletFiniteZeroFree
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.CharacterSums.DirichletFiniteZeroFree

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℂ (fun _ => ℂ → ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ s f => f s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
    χ.IsPrimitive → χ ≠ 1 → ∀ (C T ε : ℝ) (X : ℕ), 0 < ε →
    Real.exp (4 * (zeroOrder q C T ε + 1 : ℝ)) ≤ (X : ℝ) →
    (∀ j : ℕ, j ≤ gridSize T ε → ∀ k : ℕ,
      momentStart (zeroBudget q T) C (3 / 2 - ε / 2) - 1 ≤ k →
      k ≤ zeroOrder q C T ε →
      momentStart (zeroBudget q T) C (3 / 2 - ε / 2) ∣ k + 1 →
      finiteMoment χ k X (gridPoint T ε j) ≤ (C + 1 / 3) * (2 / 3 : ℝ) ^ k) →
    (∀ s : ℂ, 1 / 2 + ε ≤ s.re → |s.im| ≤ T →
      V.readout () s χ.LFunction ≠ 0) ∧
    (0 ≤ T → ∀ j : ℕ, j ≤ gridSize T ε → ∀ s : ℂ,
      ‖s - (2 + gridPoint T ε j * I)‖ ≤ 3 / 2 - ε / 2 → χ.LFunction s ≠ 0)

private theorem primitive_of_prime {p : ℕ} [NeZero p] (hp : p.Prime)
    {χ : DirichletCharacter ℂ p} (hne : χ ≠ 1) : χ.IsPrimitive := by
  rcases hp.eq_one_or_self_of_dvd χ.conductor χ.conductor_dvd_level with h | h
  · exact (hne (χ.eq_one_iff_conductor_eq_one.mpr h)).elim
  · exact h

private theorem primitive_exists :
    ∃ χ : DirichletCharacter ℂ 3, χ.IsPrimitive ∧ χ ≠ 1 := by
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity
    ℂ (show (-1 : ZMod 3) ≠ 1 by decide)
  have hne : χ ≠ 1 := by
    intro h
    rw [h] at hχ
    exact hχ (MulChar.one_apply (isUnit_one.neg))
  exact ⟨χ, primitive_of_prime (by norm_num) hne, hne⟩

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨χ, hχ, hne⟩ := primitive_exists
  let N := zeroOrder 3 0 0 3
  let X : ℕ := ⌈Real.exp (4 * (N + 1 : ℝ))⌉₊
  let C : ℝ := ∑ k ∈ Finset.range (N + 1),
    |finiteMoment χ k X 0| * (3 / 2 : ℝ) ^ k
  have horder (c : ℝ) : zeroOrder 3 c 0 3 = N := by
    dsimp only [N]
    norm_num [zeroOrder, momentOrder, momentStart]
  have hx : Real.exp (4 * (zeroOrder 3 C 0 3 + 1 : ℝ)) ≤ (X : ℝ) := by
    rw [horder]
    exact Nat.le_ceil _
  have hm : ∀ j : ℕ, j ≤ gridSize 0 3 → ∀ k : ℕ,
      momentStart (zeroBudget 3 0) C (3 / 2 - 3 / 2) - 1 ≤ k →
      k ≤ zeroOrder 3 C 0 3 →
      momentStart (zeroBudget 3 0) C (3 / 2 - 3 / 2) ∣ k + 1 →
      finiteMoment χ k X (gridPoint 0 3 j) ≤ (C + 1 / 3) * (2 / 3 : ℝ) ^ k := by
    intro j _ k _ hk _
    rw [horder] at hk
    have hs : |finiteMoment χ k X 0| * (3 / 2 : ℝ) ^ k ≤ C :=
      Finset.single_le_sum
        (f := fun l : ℕ => |finiteMoment χ l X 0| * (3 / 2 : ℝ) ^ l)
        (fun l _ => mul_nonneg (abs_nonneg _) (by positivity))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    have hp : (3 / 2 : ℝ) ^ k * (2 / 3 : ℝ) ^ k = 1 := by
      rw [← mul_pow]; norm_num
    have hb : |finiteMoment χ k X 0| ≤ C * (2 / 3 : ℝ) ^ k := by
      calc
        _ = (|finiteMoment χ k X 0| * (3 / 2 : ℝ) ^ k) * (2 / 3 : ℝ) ^ k := by
          rw [mul_assoc, hp, mul_one]
        _ ≤ _ := mul_le_mul_of_nonneg_right hs (by positivity)
    have hb' : finiteMoment χ k X 0 ≤ (C + 1 / 3) * (2 / 3 : ℝ) ^ k := by
      nlinarith [le_abs_self (finiteMoment χ k X 0),
        pow_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) k]
    simpa only [gridPoint, mul_zero, zero_mul, zero_div, neg_zero, add_zero] using hb'
  have hf := (h hχ hne C 0 3 X (by norm_num) hx hm).1 (4 : ℂ)
    (by norm_num) (by norm_num)
  exact hf rfl

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨0, (fun _ => 0), (fun _ => 1), by norm_num [actual, realize]⟩

def family : Registration arena (type_of% @finite_moment_zero_free) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_moment_zero_free, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_moment_zero_free) (Realization signature) Type Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletFiniteZeroFree.finite_moment_zero_free "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletFiniteZeroFree.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ s f => f s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletFiniteZeroFree
    definition := none
    coordinates := #[12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.CharacterSums.DirichletFiniteZeroFree
