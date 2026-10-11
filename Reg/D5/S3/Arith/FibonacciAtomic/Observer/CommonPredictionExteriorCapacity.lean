import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionExteriorCapacity
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
namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionExteriorCapacity
local notation "W" => Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : P)

namespace ExteriorAppend
abbrev sig := Reg.Support.SingleDependentReadout.signature (ℕ)
  (fun _p => Input (_p + 3)) (fun _p => Fin 3)
def actual : Realization sig := realize sig (fun _ _ x => ExteriorCounts.exteriorSelector x) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ _ _ => 2) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ {m : ℕ} (p : Fin m → W) (q r v : W), R.readout () m (Fin.append p ![q,r,v]) = MajorityGeometry.selector m (WordCounts.highN p) q r v (if WordCounts.highN p = 0 then MajorityGeometry.anchorCoin q r v else WordCounts.prefixCoin p)⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb := h (m := 0) (fun i => nomatch i) .zero .zero .zero
  norm_num [bad, realize, WordCounts.highN, MajorityGeometry.selector,
    MajorityGeometry.firstTop, MajorityGeometry.lastTop, MajorityGeometry.top0,
    MajorityGeometry.top1, MajorityGeometry.top2, MajorityGeometry.vt,
    MajorityGeometry.delta, MajorityGeometry.ld, MajorityGeometry.err,
    MajorityGeometry.aLabel, MajorityGeometry.bLabel, first, last, Fin.ext_iff] at hb
  exact (by decide : (2 : Fin 3) ≠ 0) hb
def registration : Registration arena (type_of% (@ExteriorCounts.exterior_append)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ExteriorCounts.exterior_append, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    refine ⟨1, Fin.append (fun _ : Fin 1 => .zero) ![.zero,.zero,.zero],
      Fin.append (fun _ : Fin 1 => .high) ![.low,.low,.zero], ?_⟩
    dsimp only [actual, realize]
    rw [ExteriorCounts.exterior_append, ExteriorCounts.exterior_append]
    norm_num [WordCounts.highN, WordCounts.hb, MajorityGeometry.selector,
      MajorityGeometry.firstTop, MajorityGeometry.lastTop, MajorityGeometry.top0,
      MajorityGeometry.top1, MajorityGeometry.top2, MajorityGeometry.vt,
      MajorityGeometry.delta, MajorityGeometry.ld, MajorityGeometry.err,
      MajorityGeometry.aLabel, MajorityGeometry.bLabel, first, last, Fin.ext_iff]
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ExteriorCounts.exterior_append) (type_of% (realize.{0,0,0,0,0} sig (fun _ _ x => ExteriorCounts.exteriorSelector x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.ExteriorCounts.exterior_append.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionExteriorCapacity.ExteriorAppend.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ x => ExteriorCounts.exteriorSelector x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionExteriorCapacity, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end ExteriorAppend

namespace VotesAppend
abbrev sig := Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, Fin 3)
  (fun _p => Input (_p.1 + 3)) (fun _p => ℕ)
def actual : Realization sig := realize sig (fun _ p x => ExteriorCounts.actualVotes x p.2) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ {m : ℕ} (p : Fin m → W) (q r v : W) (c : Fin 3), R.readout () ⟨m,c⟩ (Fin.append p ![q,r,v]) = MajorityGeometry.vt m (WordCounts.highN p) q r v c⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb := h (m := 0) (fun i => nomatch i) .zero .zero .zero 0
  change 1 = 0 at hb
  contradiction
def registration : Registration arena (type_of% (@ExteriorCounts.actual_votes_append)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ExteriorCounts.actual_votes_append, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    refine ⟨⟨1,0⟩, Fin.append (fun _ : Fin 1 => .zero) ![.zero,.zero,.zero],
      Fin.append (fun _ : Fin 1 => .high) ![.low,.low,.zero], ?_⟩
    change ExteriorCounts.actualVotes _ 0 ≠ ExteriorCounts.actualVotes _ 0
    rw [ExteriorCounts.actual_votes_append, ExteriorCounts.actual_votes_append]
    norm_num [WordCounts.highN, WordCounts.hb, MajorityGeometry.vt,
      MajorityGeometry.aLabel, MajorityGeometry.bLabel, first, last, Fin.ext_iff]
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ExteriorCounts.actual_votes_append) (type_of% (realize.{0,0,0,0,0} sig (fun _ p x => ExteriorCounts.actualVotes x p.2) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.ExteriorCounts.actual_votes_append.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionExteriorCapacity.VotesAppend.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ p x => ExteriorCounts.actualVotes x p.2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionExteriorCapacity, definition := none,
    coordinates := #[0, 5], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end VotesAppend

namespace ExteriorMajority
abbrev sig := Reg.Support.SingleDependentReadout.signature (Σ m : ℕ, Input (m + 3))
  (fun _p => Fin 3) (fun _p => ℕ)
def actual : Realization sig := realize sig (fun _ p c => ExteriorCounts.actualVotes p.2 c) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ _ _ => 3) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ {m : ℕ} (x : Input (m + 3)) (c : Fin 3), R.readout () ⟨m,x⟩ c ≤ ExteriorCounts.actualVotes x (ExteriorCounts.exteriorSelector x)⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hb := h (m := 1) (fun _ => .zero) 0
  change 3 ≤ ExteriorCounts.actualVotes (m := 1) (fun _ => .zero)
    (ExteriorCounts.exteriorSelector (fun _ => .zero)) at hb
  generalize ExteriorCounts.exteriorSelector (m := 1) (fun _ => .zero) = c at hb
  fin_cases c <;> norm_num [ExteriorCounts.actualVotes, teacher, TeacherLabels.leftRoles,
    TeacherLabels.rightRoles, LegalPriorityTeacher.gate, first, last, Fin.ext_iff] at hb
def registration : Registration arena (type_of% (@ExteriorCounts.exterior_majority)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ExteriorCounts.exterior_majority, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    refine ⟨⟨1,Fin.append (fun _ : Fin 1 => .zero) ![.zero,.zero,.zero]⟩, 0, 1, ?_⟩
    change ExteriorCounts.actualVotes _ 0 ≠ ExteriorCounts.actualVotes _ 1
    rw [ExteriorCounts.actual_votes_append, ExteriorCounts.actual_votes_append]
    norm_num [WordCounts.highN, WordCounts.hb, MajorityGeometry.vt,
      MajorityGeometry.aLabel, MajorityGeometry.bLabel, first, last, Fin.ext_iff]
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ExteriorCounts.exterior_majority) (type_of% (realize.{0,0,0,0,0} sig (fun _ p c => ExteriorCounts.actualVotes p.2 c) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.ExteriorCounts.exterior_majority.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionExteriorCapacity.ExteriorMajority.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ p c => ExteriorCounts.actualVotes p.2 c) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionExteriorCapacity, definition := none,
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
end ExteriorMajority

namespace UniformBalance
abbrev sig := Reg.Support.SingleDependentReadout.signature (Σ m : ℕ, Input (m + 3))
  (fun _p => Fin 3) (fun _p => ℕ)
def actual : Realization sig := realize sig (fun _ p c => ExteriorCounts.actualVotes p.2 c) (fun e => nomatch e)
def bad : Realization sig := realize sig (fun _ _ _ => 3) (fun e => nomatch e)
abbrev arena : Arena := ⟨sig, fun R => ∀ m : ℕ, 0 < m → ∃ f : Input (m + 3) → Fin 3, (∀ x c, R.readout () ⟨m,x⟩ c ≤ ExteriorCounts.actualVotes x (f x)) ∧ (∀ z, ∀ i j : Fin m, CommonSelector.errorCount z false i f = CommonSelector.errorCount z false j f ∧ CommonSelector.errorCount z false i f = CommonSelector.errorCount z true j f)⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨f,hf,_⟩ := h 1 (by decide)
  have hb := hf (fun _ => .zero) 0
  change 3 ≤ ExteriorCounts.actualVotes (m := 1) (fun _ => .zero) (f (fun _ => .zero)) at hb
  generalize f (fun _ => .zero) = c at hb
  fin_cases c <;> norm_num [ExteriorCounts.actualVotes, teacher, TeacherLabels.leftRoles,
    TeacherLabels.rightRoles, LegalPriorityTeacher.gate, first, last, Fin.ext_iff] at hb
def registration : Registration arena (type_of% (@CommonSelector.uniform_mass_balanced)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@CommonSelector.uniform_mass_balanced, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence sig actual
    intro ⟨⟩
    refine ⟨⟨1,Fin.append (fun _ : Fin 1 => .zero) ![.zero,.zero,.zero]⟩, 0, 1, ?_⟩
    change ExteriorCounts.actualVotes _ 0 ≠ ExteriorCounts.actualVotes _ 1
    rw [ExteriorCounts.actual_votes_append, ExteriorCounts.actual_votes_append]
    norm_num [WordCounts.highN, WordCounts.hb, MajorityGeometry.vt,
      MajorityGeometry.aLabel, MajorityGeometry.bLabel, first, last, Fin.ext_iff]
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@CommonSelector.uniform_mass_balanced) (type_of% (realize.{0,0,0,0,0} sig (fun _ p c => ExteriorCounts.actualVotes p.2 c) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.CommonSelector.uniform_mass_balanced.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionExteriorCapacity.UniformBalance.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sig (fun _ p c => ExteriorCounts.actualVotes p.2 c) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionExteriorCapacity, definition := some { owner := `D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionExteriorCapacity, name := `D5.S3.Arith.FibonacciAtomic.CommonPrediction.CommonSelector.UniformMassBalanced, path := #[] },
    coordinates := #[0, 3], readouts := #[{
      path := #["body", "body", "arg", "body", "fn", "arg", "body", "body", "fn", "arg"],
      stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end UniformBalance

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionExteriorCapacity
