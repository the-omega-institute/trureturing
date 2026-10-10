import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.CommonPrediction
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window first last)
open _root_.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher (Input teacher)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
set_option maxRecDepth 2048
namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts
local notation "W" => Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : P)

namespace Slice
abbrev sig := Reg.Support.SingleDependentReadout.signature (ℕ)
  (fun _p => ℕ) (fun _p => P)
def actual : Realization sig := realize sig (fun _ n k => WordCounts.slice n k) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ n k : ℕ, R.readout () n k = (n.choose k : P) * (2 * X) ^ k * (2 + X) ^ (n - k)⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have h0 := h 0 0
  norm_num [bad, realize] at h0
def registration : Registration arena (type_of% (@WordCounts.slice_formula)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@WordCounts.slice_formula, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    refine ⟨1, 0, 2, ?_⟩
    change WordCounts.slice 1 0 ≠ WordCounts.slice 1 2
    intro h
    have hc := congrArg (fun p : P => p.coeff 0) h
    norm_num [WordCounts.slice_formula] at hc
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@WordCounts.slice_formula) (type_of% (realize.{0,0,0,0,0} sig (fun _ n k => WordCounts.slice n k) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.WordCounts.slice_formula.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts.Slice.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ n k => WordCounts.slice n k) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body", "body", "fn", "arg"],
      stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Slice

namespace HighBound
abbrev sig := Reg.Support.SingleDependentReadout.signature (ℕ)
  (fun _p => Fin _p → W) (fun _p => ℕ)
def actual : Realization sig := realize sig (fun _ _ p => WordCounts.highN p) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ n _ => n + 1) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ {n : ℕ} (p : Fin n → W), R.readout () n p ≤ n⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb := h (n := 0) (fun i => nomatch i)
  norm_num [bad, realize] at hb
def registration : Registration arena (type_of% (@WordCounts.high_n_le)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@WordCounts.high_n_le, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    refine ⟨1, (fun _ => .zero), (fun _ => .high), ?_⟩
    norm_num [actual, realize, WordCounts.highN, WordCounts.hb, last]
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@WordCounts.high_n_le) (type_of% (realize.{0,0,0,0,0} sig (fun _ _ p => WordCounts.highN p) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.WordCounts.high_n_le.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts.HighBound.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ p => WordCounts.highN p) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body", "body", "fn", "arg"],
      stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end HighBound

namespace HighStrict
abbrev sig := Reg.Support.SingleDependentReadout.signature (ℕ)
  (fun _p => Fin _p → W) (fun _p => ℕ)
def actual : Realization sig := realize sig (fun _ _ p => WordCounts.highN p) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ n _ => n + 1) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ {n : ℕ} (p : Fin n → W) (i : Fin n), last (p i) = false → R.readout () n p < n⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb := h (n := 1) (fun _ => .zero) 0 rfl
  norm_num [bad, realize] at hb
def registration : Registration arena (type_of% (@WordCounts.high_n_last_false)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@WordCounts.high_n_last_false, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    refine ⟨1, (fun _ => .zero), (fun _ => .high), ?_⟩
    norm_num [actual, realize, WordCounts.highN, WordCounts.hb, last]
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@WordCounts.high_n_last_false) (type_of% (realize.{0,0,0,0,0} sig (fun _ _ p => WordCounts.highN p) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.WordCounts.high_n_last_false.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts.HighStrict.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ p => WordCounts.highN p) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"],
      stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end HighStrict

namespace ZeroLast
abbrev sig := Reg.Support.SingleDependentReadout.signature (Unit)
  (fun _p => W) (fun _p => Bool)
def actual : Realization sig := realize sig (fun _ _ a => last a) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ _ _ => true) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ {n : ℕ} (p : Fin n → W) (i : Fin n), WordCounts.highN p = 0 → R.readout () () (p i) = false⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb := h (n := 1) (fun _ => .zero) 0 (by simp [WordCounts.highN, WordCounts.hb, last])
  change true = false at hb
  contradiction
def registration : Registration arena (type_of% (@WordCounts.high_n_zero_last)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@WordCounts.high_n_zero_last, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    exact ⟨(), .zero, .high, by change false ≠ true; decide⟩
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@WordCounts.high_n_zero_last) (type_of% (realize.{0,0,0,0,0} sig (fun _ _ a => last a) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.WordCounts.high_n_zero_last.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts.ZeroLast.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ a => last a) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end ZeroLast

namespace PrefixGenerating
abbrev sig := Reg.Support.SingleDependentReadout.signature (Unit)
  (fun _p => ℕ) (fun _p => Polynomial ℕ)
def actual : Realization sig := realize sig (fun _ _ m => ∑ x : Fin m → W, (Polynomial.X : Polynomial ℕ) ^ WordCounts.rareN x) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ m : ℕ, R.readout () () m = (2 + 3 * (Polynomial.X : Polynomial ℕ)) ^ m⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb := h 0
  norm_num [bad, realize] at hb
def registration : Registration arena (type_of% (@ReservoirWords.prefix_generating)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ReservoirWords.prefix_generating, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    refine ⟨(), 0, 1, ?_⟩
    change (∑ x : Fin 0 → W, (Polynomial.X : Polynomial ℕ) ^ WordCounts.rareN x) ≠
      ∑ x : Fin 1 → W, (Polynomial.X : Polynomial ℕ) ^ WordCounts.rareN x
    rw [ReservoirWords.prefix_generating, ReservoirWords.prefix_generating]
    intro h
    have hc := congrArg (fun p : Polynomial ℕ => p.coeff 0) h
    norm_num at hc
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReservoirWords.prefix_generating) (type_of% (realize.{0,0,0,0,0} sig (fun _ _ m => ∑ x : Fin m → W, (Polynomial.X : Polynomial ℕ) ^ WordCounts.rareN x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.ReservoirWords.prefix_generating.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts.PrefixGenerating.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ m => ∑ x : Fin m → W, (Polynomial.X : Polynomial ℕ) ^ WordCounts.rareN x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end PrefixGenerating

namespace ForcedPositive
abbrev sig := Reg.Support.SingleDependentReadout.signature (Σ n : ℕ, Fin n)
  (fun _p => ℕ) (fun _p => P)
def actual : Realization sig := realize sig (fun _ u k => ∑ p : Fin u.1 → W, if WordCounts.highN p = k ∧ last (p u.2) = false then X ^ WordCounts.rareN p else 0) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ {n : ℕ} (i : Fin n) (k : ℕ), R.readout () ⟨n,i⟩ k = (2 + X) * WordCounts.slice (n - 1) k⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb := h (n := 1) 0 0
  simp [bad, realize, WordCounts.slice_formula] at hb
  have hc := congrArg (fun p : P => p.coeff 0) hb
  norm_num at hc
def registration : Registration arena (type_of% (@WordCounts.forced_positive_slice)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@WordCounts.forced_positive_slice, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    refine ⟨⟨1,0⟩, 0, 1, ?_⟩
    change (∑ p : Fin 1 → W, if WordCounts.highN p = 0 ∧ last (p 0) = false then X ^ WordCounts.rareN p else 0) ≠
      ∑ p : Fin 1 → W, if WordCounts.highN p = 1 ∧ last (p 0) = false then X ^ WordCounts.rareN p else 0
    rw [WordCounts.forced_positive_slice, WordCounts.forced_positive_slice]
    intro h
    have hc := congrArg (fun p : P => p.coeff 0) h
    norm_num [WordCounts.slice_formula] at hc
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@WordCounts.forced_positive_slice) (type_of% (realize.{0,0,0,0,0} sig (fun _ u k => ∑ p : Fin u.1 → W, if WordCounts.highN p = k ∧ last (p u.2) = false then X ^ WordCounts.rareN p else 0) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.WordCounts.forced_positive_slice.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts.ForcedPositive.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ u k => ∑ p : Fin u.1 → W, if WordCounts.highN p = k ∧ last (p u.2) = false then X ^ WordCounts.rareN p else 0) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts, definition := none,
    coordinates := #[0, 1], readouts := #[{
      path := #["body", "body", "body", "fn", "arg"],
      stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end ForcedPositive

namespace ForcedCoin
abbrev sig := Reg.Support.SingleDependentReadout.signature (Σ n : ℕ, Σ _ : Fin n, Bool)
  (fun _p => ℕ) (fun _p => P)
def actual : Realization sig := realize sig (fun _ u k => ∑ p : Fin u.1 → W, if WordCounts.highN p = k ∧ last (p u.2.1) = u.2.2 ∧ WordCounts.prefixCoin p = false then X ^ WordCounts.rareN p else 0) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ u k => (∑ p : Fin u.1 → W, if WordCounts.highN p = k ∧ last (p u.2.1) = u.2.2 ∧ WordCounts.prefixCoin p = true then X ^ WordCounts.rareN p else 0) + 1) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ {n : ℕ} (i : Fin n) (h : Bool) (k : ℕ), 0 < k → R.readout () ⟨n,i,h⟩ k = (∑ p : Fin n → W, if WordCounts.highN p = k ∧ last (p i) = h ∧ WordCounts.prefixCoin p = true then X ^ WordCounts.rareN p else 0)⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb := h (n := 1) 0 true 1 (by decide)
  change _ + 1 = _ at hb
  exact one_ne_zero (add_left_cancel (hb.trans (add_zero _).symm))
def registration : Registration arena (type_of% (@WordCounts.forced_coin_balance)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@WordCounts.forced_coin_balance, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    refine ⟨⟨1,0,true⟩, 1, 2, ?_⟩
    change (∑ p : Fin 1 → W, if WordCounts.highN p = 1 ∧ last (p 0) = true ∧ WordCounts.prefixCoin p = false then X ^ WordCounts.rareN p else 0) ≠
      ∑ p : Fin 1 → W, if WordCounts.highN p = 2 ∧ last (p 0) = true ∧ WordCounts.prefixCoin p = false then X ^ WordCounts.rareN p else 0
    rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) W).symm, ← Equiv.sum_comp (Equiv.funUnique (Fin 1) W).symm]
    simp only [show (Finset.univ : Finset W) = {.zero,.low,.middle,.ends,.high} from rfl]
    norm_num [Equiv.funUnique, Equiv.piUnique, Fin.sum_univ_one, WordCounts.highN, WordCounts.rareN, WordCounts.hb, WordCounts.rb, WordCounts.prefixCoin, WordCounts.endsN, WordCounts.eb, last]
    decide
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@WordCounts.forced_coin_balance) (type_of% (realize.{0,0,0,0,0} sig (fun _ u k => ∑ p : Fin u.1 → W, if WordCounts.highN p = k ∧ last (p u.2.1) = u.2.2 ∧ WordCounts.prefixCoin p = false then X ^ WordCounts.rareN p else 0) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.WordCounts.forced_coin_balance.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts.ForcedCoin.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ u k => ∑ p : Fin u.1 → W, if WordCounts.highN p = k ∧ last (p u.2.1) = u.2.2 ∧ WordCounts.prefixCoin p = false then X ^ WordCounts.rareN p else 0) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts, definition := none,
    coordinates := #[0, 1, 2], readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end ForcedCoin

namespace AppendReservoir
abbrev sig := Reg.Support.SingleDependentReadout.signature (Unit)
  (fun _p => Fin 3 → W) (fun _p => W)
def actual : Realization sig := realize sig (fun _ _ a => a 1) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ _ _ => .zero) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ (m : ℕ) (p : Fin m → W) (a : Fin 3 → W), ReservoirWords.isReservoir (Fin.append p a) ↔ ReservoirWords.qok (a 0) ∧ R.readout () () a = .high ∧ ReservoirWords.vok (a 2)⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb := (h 0 (fun i => nomatch i) ![.zero,.high,.low]).mp (by simp [ReservoirWords.append_res, ReservoirWords.qok, ReservoirWords.vok])
  change _ ∧ (Window.zero = Window.high) ∧ _ at hb
  cases hb.2.1
def registration : Registration arena (type_of% (@ReservoirWords.append_res)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ReservoirWords.append_res, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    refine ⟨(), (fun _ => .zero), (fun _ => .high), ?_⟩
    change Window.zero ≠ Window.high
    decide
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReservoirWords.append_res) (type_of% (realize.{0,0,0,0,0} sig (fun _ _ a => a 1) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.ReservoirWords.append_res.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts.AppendReservoir.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ a => a 1) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg"],
      stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end AppendReservoir

namespace AppendRare
abbrev sig := Reg.Support.SingleDependentReadout.signature (ℕ)
  (fun _p => Input (_p + 3)) (fun _p => ℕ)
def actual : Realization sig := realize sig (fun _ _ x => WordCounts.rareN x) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ (m : ℕ) (p : Fin m → W) (a : Fin 3 → W), R.readout () m (Fin.append p a) = WordCounts.rareN p + (WordCounts.rb (a 0) + WordCounts.rb (a 1) + WordCounts.rb (a 2))⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb := h 0 (fun i => nomatch i) (fun _ => .zero)
  norm_num [bad, realize, WordCounts.rareN, WordCounts.rb] at hb
def registration : Registration arena (type_of% (@ReservoirWords.append_rare)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ReservoirWords.append_rare, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    refine ⟨0, (fun _ => .zero), (fun _ => .low), ?_⟩
    norm_num [actual, realize, WordCounts.rareN, WordCounts.rb]
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReservoirWords.append_rare) (type_of% (realize.{0,0,0,0,0} sig (fun _ _ x => WordCounts.rareN x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.ReservoirWords.append_rare.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts.AppendRare.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ x => WordCounts.rareN x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end AppendRare

namespace ReservoirCardinality
abbrev sig := Reg.Support.SingleDependentReadout.signature (ℕ)
  (fun _p => ℕ) (fun _p => ℕ)
def actual : Realization sig := realize sig (fun _ m z => ReservoirWords.Nz m z) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ m z : ℕ, R.readout () m z = (2 * (Polynomial.X : Polynomial ℕ) ^ 2 * (2 + Polynomial.X) * (2 + 3 * Polynomial.X) ^ m).coeff z⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb := h 0 2
  norm_num [bad, realize, mul_assoc, mul_add, add_mul] at hb
def registration : Registration arena (type_of% (@ReservoirWords.actual_nz_identity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ReservoirWords.actual_nz_identity, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    refine ⟨0, 0, 2, ?_⟩
    change ReservoirWords.Nz 0 0 ≠ ReservoirWords.Nz 0 2
    rw [ReservoirWords.actual_nz_identity, ReservoirWords.actual_nz_identity]
    norm_num [mul_assoc, mul_add, add_mul]
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReservoirWords.actual_nz_identity) (type_of% (realize.{0,0,0,0,0} sig (fun _ m z => ReservoirWords.Nz m z) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.ReservoirWords.actual_nz_identity.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts.ReservoirCardinality.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ m z => ReservoirWords.Nz m z) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body", "body", "fn", "arg"],
      stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end ReservoirCardinality

namespace PrefixPermutation
abbrev sig := Reg.Support.SingleDependentReadout.signature (ℕ)
  (fun _p => Input (_p + 3)) (fun _p => ℕ)
def actual : Realization sig := realize sig (fun _ _ x => WordCounts.rareN x) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ {m : ℕ} (p : Fin m → W) (a : Fin 3 → W) (σ : Equiv.Perm (Fin m)), R.readout () m (Fin.append (p ∘ σ) a) = WordCounts.rareN (Fin.append p a) ∧ (ReservoirWords.isReservoir (Fin.append (p ∘ σ) a) ↔ ReservoirWords.isReservoir (Fin.append p a))⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb := (h (m := 0) (fun i => nomatch i) (fun _ => .zero) (Equiv.refl _)).1
  change (1 : ℕ) = WordCounts.rareN (Fin.append (fun i : Fin 0 => nomatch i) (fun _ : Fin 3 => .zero)) at hb
  rw [ReservoirWords.append_rare] at hb
  norm_num [WordCounts.rareN, WordCounts.rb] at hb
def registration : Registration arena (type_of% (@ReservoirWords.actual_prefix_perm)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ReservoirWords.actual_prefix_perm, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    refine ⟨0, (fun _ => .zero), (fun _ => .low), ?_⟩
    norm_num [actual, realize, WordCounts.rareN, WordCounts.rb]
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReservoirWords.actual_prefix_perm) (type_of% (realize.{0,0,0,0,0} sig (fun _ _ x => WordCounts.rareN x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.ReservoirWords.actual_prefix_perm.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts.PrefixPermutation.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ x => WordCounts.rareN x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end PrefixPermutation

namespace LeftLabel
abbrev sig := Reg.Support.SingleDependentReadout.signature (Σ m : ℕ, Fin m)
  (fun _p => Input (_p.1 + 3)) (fun _p => Fin 3)
def actual : Realization sig := realize sig (fun _ u x => teacher (TeacherLabels.leftRoles u.2) x) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ _ _ => 2) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ {m : ℕ} (p : Fin m → W) (a : Fin 3 → W) (i : Fin m), R.readout () ⟨m,i⟩ (Fin.append p a) = (if last (p i) && first (a 0) then 1 else if last (a 0) && first (a 1) then 2 else 0)⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb := h (m := 1) (fun _ => .zero) (fun _ => .zero) 0
  norm_num [bad, realize, first, last, Fin.ext_iff] at hb
  exact (by decide : (2 : Fin 3) ≠ 0) hb
def registration : Registration arena (type_of% (@TeacherLabels.actual_left_label)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@TeacherLabels.actual_left_label, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    refine ⟨⟨1,0⟩, Fin.append (fun _ : Fin 1 => .zero) ![.zero,.zero,.zero],
      Fin.append (fun _ : Fin 1 => .high) ![.low,.zero,.zero], ?_⟩
    dsimp only [actual, realize]
    rw [TeacherLabels.actual_left_label, TeacherLabels.actual_left_label]
    norm_num [first, last, Fin.ext_iff]
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@TeacherLabels.actual_left_label) (type_of% (realize.{0,0,0,0,0} sig (fun _ u x => teacher (TeacherLabels.leftRoles u.2) x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.TeacherLabels.actual_left_label.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts.LeftLabel.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ u x => teacher (TeacherLabels.leftRoles u.2) x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts, definition := none,
    coordinates := #[0, 3], readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end LeftLabel

namespace RightLabel
abbrev sig := Reg.Support.SingleDependentReadout.signature (Σ m : ℕ, Fin m)
  (fun _p => Input (_p.1 + 3)) (fun _p => Fin 3)
def actual : Realization sig := realize sig (fun _ u x => teacher (TeacherLabels.rightRoles u.2) x) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ _ _ => 2) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ {m : ℕ} (p : Fin m → W) (a : Fin 3 → W) (i : Fin m), R.readout () ⟨m,i⟩ (Fin.append p a) = (if last (p i) && first (a 1) then 1 else if last (a 1) && first (a 2) then 2 else 0)⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb := h (m := 1) (fun _ => .zero) (fun _ => .zero) 0
  norm_num [bad, realize, first, last, Fin.ext_iff] at hb
  exact (by decide : (2 : Fin 3) ≠ 0) hb
def registration : Registration arena (type_of% (@TeacherLabels.actual_right_label)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@TeacherLabels.actual_right_label, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    refine ⟨⟨1,0⟩, Fin.append (fun _ : Fin 1 => .zero) ![.zero,.zero,.zero],
      Fin.append (fun _ : Fin 1 => .high) ![.zero,.low,.zero], ?_⟩
    dsimp only [actual, realize]
    rw [TeacherLabels.actual_right_label, TeacherLabels.actual_right_label]
    norm_num [first, last, Fin.ext_iff]
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@TeacherLabels.actual_right_label) (type_of% (realize.{0,0,0,0,0} sig (fun _ u x => teacher (TeacherLabels.rightRoles u.2) x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.TeacherLabels.actual_right_label.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts.RightLabel.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ u x => teacher (TeacherLabels.rightRoles u.2) x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts, definition := none,
    coordinates := #[0, 3], readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end RightLabel

namespace ReservoirFlat
abbrev sig := Reg.Support.SingleDependentReadout.signature (Σ m : ℕ, Fin m)
  (fun _p => Input (_p.1 + 3)) (fun _p => Fin 3)
def actual : Realization sig := realize sig (fun _ u x => teacher (TeacherLabels.leftRoles u.2) x) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ _ _ => 2) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ {m : ℕ} (p : Fin m → W) (q v : W), (q = .zero ∨ q = .middle ∨ q = .high) → (v = .low ∨ v = .ends) → ∀ i : Fin m, R.readout () ⟨m,i⟩ (Fin.append p ![q,.high,v]) = 0 ∧ teacher (TeacherLabels.rightRoles i) (Fin.append p ![q,.high,v]) = 2⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb := (h (m := 1) (fun _ => .zero) .zero .low (Or.inl rfl) (Or.inl rfl) 0).1
  change (2 : Fin 3) = 0 at hb
  contradiction
def registration : Registration arena (type_of% (@TeacherLabels.actual_reservoir_flat)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@TeacherLabels.actual_reservoir_flat, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    refine ⟨⟨1,0⟩, Fin.append (fun _ : Fin 1 => .zero) ![.zero,.zero,.zero],
      Fin.append (fun _ : Fin 1 => .high) ![.low,.zero,.zero], ?_⟩
    dsimp only [actual, realize]
    rw [TeacherLabels.actual_left_label, TeacherLabels.actual_left_label]
    norm_num [first, last, Fin.ext_iff]
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@TeacherLabels.actual_reservoir_flat) (type_of% (realize.{0,0,0,0,0} sig (fun _ u x => teacher (TeacherLabels.leftRoles u.2) x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.TeacherLabels.actual_reservoir_flat.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts.ReservoirFlat.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ u x => teacher (TeacherLabels.leftRoles u.2) x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts, definition := none,
    coordinates := #[0, 6], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end ReservoirFlat

namespace IntegerSplit
abbrev sig := Reg.Support.SingleDependentReadout.signature (ℕ)
  (fun _p => ℕ) (fun _p => ℤ)
def actual : Realization sig := realize sig (fun _ m z => Capacity.reservoir_half m z) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ _ _ => -1) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ (m z : ℕ), 0 < m → ∃ t : ℕ, (t : ℤ) ≤ 2 * R.readout () m z ∧ 2 * Capacity.discrepancy_half m z - 2 * Capacity.reservoir_half m z + 2 * (t : ℤ) = 0⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨t,ht,_⟩ := h 1 0 (by decide)
  change (t : ℤ) ≤ 2 * (-1) at ht
  omega
def registration : Registration arena (type_of% (@Capacity.integer_split_positive)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Capacity.integer_split_positive, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    refine ⟨1, 0, 2, ?_⟩
    change (0 : ℤ) ≠ 4
    norm_num
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Capacity.integer_split_positive) (type_of% (realize.{0,0,0,0,0} sig (fun _ m z => Capacity.reservoir_half m z) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.Capacity.integer_split_positive.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts.IntegerSplit.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ m z => Capacity.reservoir_half m z) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body", "body", "body", "arg", "body", "fn", "arg", "arg", "arg"],
      stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end IntegerSplit

namespace ZeroRegion
abbrev sig := Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, Σ _ : W, Σ _ : W, W)
  (fun _p => Bool) (fun _p => Fin 3)
def actual : Realization sig := realize sig (fun _ p b => MajorityGeometry.selector p.1 0 p.2.1 p.2.2.1 p.2.2.2 b) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ (m : ℕ), 0 < m → ∀ (q r v : W) (coin : Bool), R.readout () ⟨m,q,r,v⟩ coin = MajorityGeometry.selector 1 0 q r v coin⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb := h 1 (by decide) .zero .zero .zero false
  norm_num [bad, realize, MajorityGeometry.selector, MajorityGeometry.region, MajorityGeometry.representative, MajorityGeometry.firstTop, MajorityGeometry.lastTop, MajorityGeometry.top0, MajorityGeometry.top1, MajorityGeometry.top2, MajorityGeometry.vt, MajorityGeometry.delta, MajorityGeometry.ld, MajorityGeometry.err, MajorityGeometry.aLabel, MajorityGeometry.bLabel, first, last, Fin.ext_iff] at hb
def registration : Registration arena (type_of% (@MajorityGeometry.selector_region_zero)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@MajorityGeometry.selector_region_zero, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    refine ⟨⟨1,.high,.low,.zero⟩, false, true, ?_⟩
    norm_num [actual, realize, MajorityGeometry.selector, MajorityGeometry.firstTop,
      MajorityGeometry.lastTop, MajorityGeometry.top0, MajorityGeometry.top1,
      MajorityGeometry.top2, MajorityGeometry.vt, MajorityGeometry.delta,
      MajorityGeometry.ld, MajorityGeometry.err, MajorityGeometry.aLabel,
      MajorityGeometry.bLabel, first, last,
      show (0 : Fin 3) ≠ 1 from by decide, show (0 : Fin 3) ≠ 2 from by decide,
      show (1 : Fin 3) ≠ 0 from by decide, show (1 : Fin 3) ≠ 2 from by decide,
      show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide]
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@MajorityGeometry.selector_region_zero) (type_of% (realize.{0,0,0,0,0} sig (fun _ p b => MajorityGeometry.selector p.1 0 p.2.1 p.2.2.1 p.2.2.2 b) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.MajorityGeometry.selector_region_zero.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts.ZeroRegion.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ p b => MajorityGeometry.selector p.1 0 p.2.1 p.2.2.1 p.2.2.2 b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts, definition := none,
    coordinates := #[0, 2, 3, 4], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end ZeroRegion

namespace StableSelector
abbrev sig := Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, Σ _ : ℕ, Σ _ : W, Σ _ : W, W)
  (fun _p => Bool) (fun _p => Fin 3)
def actual : Realization sig := realize sig (fun _ p b => MajorityGeometry.selector p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 b) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ (m k : ℕ), 0 < m → k ≤ m → ∀ (q r v : W) (coin : Bool), R.readout () ⟨m,k,q,r,v⟩ coin = MajorityGeometry.selector (MajorityGeometry.representative (MajorityGeometry.region m k)).1 (MajorityGeometry.representative (MajorityGeometry.region m k)).2 q r v coin⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb := h 1 0 (by decide) (by decide) .zero .zero .zero false
  norm_num [bad, realize, MajorityGeometry.selector, MajorityGeometry.region, MajorityGeometry.representative, MajorityGeometry.firstTop, MajorityGeometry.lastTop, MajorityGeometry.top0, MajorityGeometry.top1, MajorityGeometry.top2, MajorityGeometry.vt, MajorityGeometry.delta, MajorityGeometry.ld, MajorityGeometry.err, MajorityGeometry.aLabel, MajorityGeometry.bLabel, first, last, Fin.ext_iff] at hb
def registration : Registration arena (type_of% (@MajorityGeometry.selector_stable)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@MajorityGeometry.selector_stable, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    refine ⟨⟨1,0,.high,.low,.zero⟩, false, true, ?_⟩
    norm_num [actual, realize, MajorityGeometry.selector, MajorityGeometry.firstTop,
      MajorityGeometry.lastTop, MajorityGeometry.top0, MajorityGeometry.top1,
      MajorityGeometry.top2, MajorityGeometry.vt, MajorityGeometry.delta,
      MajorityGeometry.ld, MajorityGeometry.err, MajorityGeometry.aLabel,
      MajorityGeometry.bLabel, first, last,
      show (0 : Fin 3) ≠ 1 from by decide, show (0 : Fin 3) ≠ 2 from by decide,
      show (1 : Fin 3) ≠ 0 from by decide, show (1 : Fin 3) ≠ 2 from by decide,
      show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide]
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@MajorityGeometry.selector_stable) (type_of% (realize.{0,0,0,0,0} sig (fun _ p b => MajorityGeometry.selector p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 b) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.MajorityGeometry.selector_stable.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts.StableSelector.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ p b => MajorityGeometry.selector p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts, definition := none,
    coordinates := #[0, 1, 4, 5, 6], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end StableSelector

namespace FirstMajority
abbrev sig := Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, Σ _ : ℕ, Σ _ : W, Σ _ : W, W)
  (fun _p => Fin 3) (fun _p => ℕ)
def actual : Realization sig := realize sig (fun _ p c => MajorityGeometry.vt p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 c) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ _ _ => 3) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ (m k : ℕ) (q r v : W)  (c : Fin 3), R.readout () ⟨m,k,q,r,v⟩ c ≤ MajorityGeometry.vt m k q r v (MajorityGeometry.firstTop m k q r v)⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb := h 1 0 .zero .zero .zero 0
  norm_num [bad, realize, MajorityGeometry.selector, MajorityGeometry.firstTop, MajorityGeometry.lastTop, MajorityGeometry.top0, MajorityGeometry.top1, MajorityGeometry.top2, MajorityGeometry.vt, MajorityGeometry.delta, MajorityGeometry.ld, MajorityGeometry.err, MajorityGeometry.aLabel, MajorityGeometry.bLabel, first, last, Fin.ext_iff] at hb
def registration : Registration arena (type_of% (@MajorityGeometry.first_top_majority)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@MajorityGeometry.first_top_majority, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    exact ⟨⟨1,0,.zero,.zero,.zero⟩, 0, 1, by norm_num [actual, realize, first, last, Fin.ext_iff, MajorityGeometry.selector, MajorityGeometry.region, MajorityGeometry.representative, MajorityGeometry.firstTop, MajorityGeometry.lastTop, MajorityGeometry.top0, MajorityGeometry.top1, MajorityGeometry.top2, MajorityGeometry.vt, MajorityGeometry.delta, MajorityGeometry.ld, MajorityGeometry.err, MajorityGeometry.aLabel, MajorityGeometry.bLabel]⟩
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@MajorityGeometry.first_top_majority) (type_of% (realize.{0,0,0,0,0} sig (fun _ p c => MajorityGeometry.vt p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 c) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.MajorityGeometry.first_top_majority.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts.FirstMajority.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ p c => MajorityGeometry.vt p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 c) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts, definition := none,
    coordinates := #[0, 1, 2, 3, 4], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end FirstMajority

namespace SelectorMajority
abbrev sig := Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, Σ _ : ℕ, Σ _ : W, Σ _ : W, W)
  (fun _p => Fin 3) (fun _p => ℕ)
def actual : Realization sig := realize sig (fun _ p c => MajorityGeometry.vt p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 c) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ _ _ => 3) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ (m k : ℕ) (q r v : W) (coin : Bool) (c : Fin 3), R.readout () ⟨m,k,q,r,v⟩ c ≤ MajorityGeometry.vt m k q r v (MajorityGeometry.selector m k q r v coin)⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb := h 1 0 .zero .zero .zero false 0
  norm_num [bad, realize, MajorityGeometry.selector, MajorityGeometry.firstTop, MajorityGeometry.lastTop, MajorityGeometry.top0, MajorityGeometry.top1, MajorityGeometry.top2, MajorityGeometry.vt, MajorityGeometry.delta, MajorityGeometry.ld, MajorityGeometry.err, MajorityGeometry.aLabel, MajorityGeometry.bLabel, first, last, Fin.ext_iff] at hb
def registration : Registration arena (type_of% (@MajorityGeometry.selector_majority)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@MajorityGeometry.selector_majority, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    exact ⟨⟨1,0,.zero,.zero,.zero⟩, 0, 1, by norm_num [actual, realize, first, last, Fin.ext_iff, MajorityGeometry.selector, MajorityGeometry.region, MajorityGeometry.representative, MajorityGeometry.firstTop, MajorityGeometry.lastTop, MajorityGeometry.top0, MajorityGeometry.top1, MajorityGeometry.top2, MajorityGeometry.vt, MajorityGeometry.delta, MajorityGeometry.ld, MajorityGeometry.err, MajorityGeometry.aLabel, MajorityGeometry.bLabel]⟩
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@MajorityGeometry.selector_majority) (type_of% (realize.{0,0,0,0,0} sig (fun _ p c => MajorityGeometry.vt p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 c) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.MajorityGeometry.selector_majority.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts.SelectorMajority.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ p c => MajorityGeometry.vt p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 c) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts, definition := none,
    coordinates := #[0, 1, 2, 3, 4], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end SelectorMajority

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts
