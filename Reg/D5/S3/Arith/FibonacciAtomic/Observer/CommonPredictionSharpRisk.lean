import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionSharpRisk
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.CommonPrediction
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window first last)
open _root_.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher (Input teacher)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionSharpRisk
local notation "W" => Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : P)

namespace SharpRisk
abbrev sig := Reg.Support.SingleDependentReadout.signature (Σ n : ℕ, Fin n)
  (fun _p => ℝ) (fun _p => ℝ)
def actual : Realization sig := realize sig (fun _ p s => SharpRisk.T p.2.val s) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ p s => SharpRisk.T p.2.val s + 1) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ {n : ℕ} (q r v : Fin n), 0 < q.val → ∀ (qr : q < r) (rv : r < v) (s : ℝ), 0 < s → s ≤ 1 / 5 → (∃ f : Input n → Fin 3, ∀ t, SharpRisk.gappedRisk q r v qr rv s f t = SharpRisk.T q.val s) ∧ (∀ f : Input n → Fin 3, ∃ t, SharpRisk.T q.val s ≤ SharpRisk.gappedRisk q r v qr rv s f t) ∧ (∀ ε : ℝ, (∃ f : Input n → Fin 3, ∀ t, SharpRisk.gappedRisk q r v qr rv s f t ≤ ε) ↔ R.readout () ⟨n,q⟩ s ≤ ε)⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb := (h (n := 4) 1 2 3 (by decide) (by decide) (by decide) (1/5) (by norm_num) (by norm_num)).2.2
  obtain ⟨f,hf⟩ := (SharpRisk.sharp_risk_full (n := 4) 1 2 3 (by decide) (by decide) (by decide) (1/5) (by norm_num) (by norm_num)).1
  have hc := (hb (SharpRisk.T 1 (1/5))).mp ⟨f,fun t => (hf t).le⟩
  change SharpRisk.T 1 (1/5) + 1 ≤ SharpRisk.T 1 (1/5) at hc
  linarith
def registration : Registration arena (type_of% (@SharpRisk.sharp_risk_full)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@SharpRisk.sharp_risk_full, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    refine ⟨⟨2,1⟩, 0, 1, ?_⟩
    change SharpRisk.T 1 0 ≠ SharpRisk.T 1 1
    unfold SharpRisk.T
    norm_num [Finset.sum_range_succ]
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@SharpRisk.sharp_risk_full) (type_of% (realize.{0,0,0,0,0} sig (fun _ p s => SharpRisk.T p.2.val s) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.SharpRisk.sharp_risk_full.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionSharpRisk.SharpRisk.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ p s => SharpRisk.T p.2.val s) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionSharpRisk, definition := none,
    coordinates := #[0, 1], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "arg", "fn", "arg"],
      stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end SharpRisk

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionSharpRisk
