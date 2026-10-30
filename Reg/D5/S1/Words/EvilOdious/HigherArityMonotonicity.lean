import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.EvilOdious.HigherArityMonotonicity
import Reg.Support.SingleDependentReadout

/-! # Escape Registration for Higher-Arity Evil-Odious Monotonicity -/

namespace Reg.D5.S1.Words.EvilOdious.HigherArityMonotonicity

open _root_.D5.S1.Words.Complexity
open _root_.D5.S1.Words.EvilOdious.SequenceCoefficients
open _root_.D5.S1.Words.EvilOdious.HigherArityMonotonicity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

namespace PairConvolutionAndBound

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ q => 2 * q) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O :=
    (∀ q : ℕ, evilInd (O.readout () () q) + evilInd (2 * q + 1) = 1) ∧
    (∀ q : ℕ, odiousInd (2 * q) + odiousInd (2 * q + 1) = 1) ∧
    (∀ n : ℕ, (evilInd n = 0 ∨ evilInd n = 1) ∧ (odiousInd n = 0 ∨ odiousInd n = 1) ∧
      r 1 n = evilInd n ∧ s 1 n = odiousInd n) ∧
    (∀ k n : ℕ, r (k + 1) n = natConv evilInd (r k) n ∧
      s (k + 1) n = natConv odiousInd (s k) n) ∧
    (∀ k n : ℕ, 1 ≤ k →
      r k n ≤ Nat.choose (n + k - 1) (k - 1) ∧
      s k n ≤ Nat.choose (n + k - 1) (k - 1)) ∧
    (∀ k n : ℕ, positiveEvilCount k (n + k) = r k n ∧
      positiveOdiousCount k (n + k) = s k n)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 : evilInd 1 + evilInd 1 = 1 := h.1 0
  have htm1 : thueMorse 1 = true := by simpa using thueMorse_two_mul_add_one 0
  simp [evilInd, htm1] at h0

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩

def evidence : Registration arena
    (type_of% (@evil_odious_pair_convolution_and_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨evil_odious_pair_convolution_and_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@evil_odious_pair_convolution_and_bound)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ q => 2 * q) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S1.Words.EvilOdious.HigherArityMonotonicity.PairConvolutionAndBound.unit
  realizationName :=
    `Reg.D5.S1.Words.EvilOdious.HigherArityMonotonicity.PairConvolutionAndBound.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ q => 2 * q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.EvilOdious.HigherArityMonotonicity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PairConvolutionAndBound

namespace QuantifiedPrefixCorrection

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ k => k) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O :=
    ∀ (a f : ℕ → ℕ) (R : ℕ),
      (∀ q : ℕ, a (2 * q) + a (2 * q + 1) = 1) →
      (∀ m : ℕ, R ≤ m → (1 : ℤ) ≤ fwdDiff f m) →
      (∀ m : ℕ, a m = 0 ∨ a m = 1) ∧
      ((prefixVar R f : ℤ) = prefixVarInt R f) ∧
      (∀ n : ℕ, R ≤ n →
        fwdDiff (natConv a f) n =
          (a (n + 1) : ℤ) * (f 0 : ℤ) +
            (∑ m ∈ Finset.range R, (a (n - m) : ℤ) * fwdDiff f m) +
            (∑ j ∈ Finset.range (n - R + 1), (a j : ℤ) * fwdDiff f (n - j)) ∧
        (a (n + 1) : ℤ) * (f 0 : ℤ) + (((n - R + 1) / 2 : ℕ) : ℤ) -
            (∑ m ∈ Finset.range R, (a (n - m) : ℤ) *
              _root_.D5.S1.Words.EvilOdious.HigherArityMonotonicity.negPart (fwdDiff f m)) ≤
          fwdDiff (natConv a f) n ∧
        (a (n + 1) : ℤ) * (f 0 : ℤ) + (((n - R + 1) / 2 : ℕ) : ℤ) - prefixVarInt R f ≤
          (a (n + 1) : ℤ) * (f 0 : ℤ) + (((n - R + 1) / 2 : ℕ) : ℤ) -
            (∑ m ∈ Finset.range R, (a (n - m) : ℤ) *
              _root_.D5.S1.Words.EvilOdious.HigherArityMonotonicity.negPart (fwdDiff f m)) ∧
        (a (n + 1) : ℤ) * (f 0 : ℤ) + (((n - R + 1) / 2 : ℕ) : ℤ) - prefixVarInt R f ≤
          fwdDiff (natConv a f) n) ∧
      (∀ n : ℕ, R + 2 * prefixVar R f + 1 ≤ n → (1 : ℤ) ≤ fwdDiff (natConv a f) n) ∧
      (∀ k : ℕ, 1 ≤ k →
        (∑ m ∈ Finset.range R, Nat.choose (m + k - 1) (k - 1)) =
          Nat.choose (R + k - 1) (O.readout () () k)) ∧
      (∀ k : ℕ, 1 ≤ k → (∀ m : ℕ, f m ≤ Nat.choose (m + k - 1) (k - 1)) →
        prefixVar R f ≤ Nat.choose (R + k - 1) k ∧
        (∀ n : ℕ, R + 2 * Nat.choose (R + k - 1) k + 1 ≤ n →
          (1 : ℤ) ≤ fwdDiff (natConv a f) n))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha : ∀ q : ℕ, (2 * q) % 2 + (2 * q + 1) % 2 = 1 := fun q => by omega
  have hf : ∀ m : ℕ, 2 ≤ m → (1 : ℤ) ≤ fwdDiff (fun x => x) m := by
    intro m _; unfold fwdDiff; push_cast; omega
  have hk := (h (fun n => n % 2) (fun m => m) 2 ha hf).2.2.2.2.1 1 le_rfl
  exact absurd hk (by decide)

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, Nat.zero_ne_one⟩

def evidence : Registration arena
    (type_of% (@quantified_finite_prefix_correction)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨quantified_finite_prefix_correction, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@quantified_finite_prefix_correction)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ k => k) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S1.Words.EvilOdious.HigherArityMonotonicity.QuantifiedPrefixCorrection.unit
  realizationName :=
    `Reg.D5.S1.Words.EvilOdious.HigherArityMonotonicity.QuantifiedPrefixCorrection.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ k => k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.EvilOdious.HigherArityMonotonicity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg", "arg",
        "fn", "arg", "body", "body", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end QuantifiedPrefixCorrection

namespace HigherArityStrictMonotonicity

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ k => k + 1) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 6) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O :=
    evilBound 6 = 37 ∧
    odiousBound 6 = 5 ∧
    (∀ k : ℕ, 6 ≤ k →
      evilBound (k + 1) = evilBound k + 2 * Nat.choose (evilBound k + k - 1) k + 1 ∧
      odiousBound (O.readout () () k) =
        odiousBound k + 2 * Nat.choose (odiousBound k + k - 1) k + 1) ∧
    evilBound 7 = 38 + 2 * Nat.choose 42 6 ∧
    odiousBound 7 = 426 ∧
    (∀ k : ℕ, 1 ≤ k →
      shiftedOdious k 0 = 1 ∧
      (∀ n : ℕ, n < k → s k n = 0) ∧
      (∀ n : ℕ, k ≤ n → s k n = shiftedOdious k (n - k))) ∧
    (∀ k : ℕ, 6 ≤ k → ∀ m : ℕ, shiftedOdious k m < shiftedOdious k (m + 1)) ∧
    (∀ k : ℕ, 6 ≤ k → ∀ n : ℕ, k - 1 ≤ n → s k n < s k (n + 1)) ∧
    (∀ k : ℕ, 6 ≤ k → ∀ n : ℕ, evilBound k ≤ n → r k n < r k (n + 1)) ∧
    (∀ k : ℕ, 6 ≤ k → ∀ n : ℕ, odiousBound k ≤ n → s k n < s k (n + 1))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h6 : odiousBound 6 = odiousBound 6 + 2 * Nat.choose (odiousBound 6 + 6 - 1) 6 + 1 :=
    (h.2.2.1 6 le_rfl).2
  exact absurd h6 (by decide)

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩

def evidence : Registration arena
    (type_of% (@higher_arity_evil_odious_strict_monotonicity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨higher_arity_evil_odious_strict_monotonicity, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@higher_arity_evil_odious_strict_monotonicity)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ k => k + 1) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S1.Words.EvilOdious.HigherArityMonotonicity.HigherArityStrictMonotonicity.unit
  realizationName :=
    `Reg.D5.S1.Words.EvilOdious.HigherArityMonotonicity.HigherArityStrictMonotonicity.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ k => k + 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.EvilOdious.HigherArityMonotonicity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "fn", "arg", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end HigherArityStrictMonotonicity

end Reg.D5.S1.Words.EvilOdious.HigherArityMonotonicity
