import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.CompleteFailure
import Reg.Support.SingleDependentReadout

/-! Source-bound audit attempts keep the complete unrestricted theorem telescopes. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.Linear.GainRay
open _root_.D5.S3.Observer.CubicGain
open _root_.D5.S3.Observer.CubicGain.CompleteFailure

open scoped Classical
noncomputable section
namespace Reg.D5.S3.Observer.CubicGain.CompleteFailure

private def src : Mat := sourceChart 1 1
private theorem src_legal : LegalSource src := source_chart_legal 1 1 (by norm_num) (by norm_num)
private def coeff (d : ℕ) : Coeff d := fun _ => 1
private theorem coeff_ne (d : ℕ) : coeff d ≠ 0 := by
  intro h
  have hh := congrFun h ⟨0, by omega⟩
  norm_num [coeff] at hh
private def target (d : ℕ) (δ : ℝ) : World d := ⟨src, src_legal, coeff d, coeff_ne d, δ⟩
private def twin (d : ℕ) : World d :=
  ⟨sourceChart 2 1, source_chart_legal 2 1 (by norm_num) (by norm_num),
    coeff d, coeff_ne d, 0⟩
private theorem target_ne (d : ℕ) : target d 0 ≠ twin d := by
  intro h
  have hh := congrArg (fun W : World d => W.source 0 0) h
  norm_num [target, twin, src, sourceChart] at hh
private def pair (d : ℕ) : Set (World d) := {target d 0, twin d}
private theorem pair_guard (d : ℕ) : (pair d).Nontrivial := by
  exact ⟨target d 0, by simp [pair], twin d, by simp [pair], target_ne d⟩

namespace Legal
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => Mat) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ P => P.det) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ P : Mat,
    LegalSource P ↔ (∀ i j, 0 < P i j) ∧ R.readout () () P = 0 ∧ Matrix.trace P = 1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := ((h src).mp src_legal).2.1
  change (1 : ℝ) = 0 at hh
  exact one_ne_zero hh
def family : Registration arena (type_of% @legal_source_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨legal_source_iff, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : Mat), 1, ?_⟩
    norm_num [actual, realize]
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@legal_source_iff) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.CompleteFailure.legal_source_iff.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.CompleteFailure.Legal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ P => P.det) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.CompleteFailure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","arg","arg","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Legal

namespace Domain
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature ℕ
  Coeff (fun _ => Polynomial ℝ)
def actual : Realization signature := realize signature (fun _ d c => gain d c) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ) (P : Mat) (p : Polynomial ℝ) (δ : ℝ),
    (∃ W : World d, W.source = P ∧ R.readout () d W.coeff = p ∧ W.drift = δ) ↔
      (∀ i j, 0 < P i j) ∧ P.det = 0 ∧ Matrix.trace P = 1 ∧ p ≠ 0 ∧ p.natDegree ≤ d
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨hp, hd, ht⟩ := (legal_source_iff src).mp src_legal
  obtain ⟨W, _, hh, _⟩ := (h 0 src 1 0).mpr ⟨hp, hd, ht, one_ne_zero, by simp⟩
  change (0 : Polynomial ℝ) = 1 at hh
  exact zero_ne_one hh
def family : Registration arena (type_of% @whole_domain) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨whole_domain, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, coeff 0, ?_⟩
    intro h
    have hh := congrArg (fun p : Polynomial ℝ => p.coeff 0) h
    norm_num [actual, realize, gain, coeff] at hh
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@whole_domain) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.CompleteFailure.whole_domain.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.CompleteFailure.Domain.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ d c => gain d c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.CompleteFailure
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","fn","arg","arg","body","arg","fn","arg","fn","arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Domain

namespace Mono
abbrev Param := Σ d : ℕ, ℕ × List Bool
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Param
  (fun p => Set (World p.1)) (fun _ => Prop)
def actual : Realization signature := realize signature
  (fun _ p K => Loses p.2.1 K p.2.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d n : ℕ} {K K' : Set (World d)} {v : List Bool},
    Loses n K v → K ⊆ K' → R.readout () ⟨d, n, v⟩ K'
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (d := 0) (n := 0) (K := pair 0) (K' := pair 0) (v := [])
    (pair_guard 0) (Set.Subset.refl (pair 0))
def family : Registration arena (type_of% @loses_mono) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@loses_mono, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨0, 0, []⟩, ∅, pair 0, ?_⟩
    intro h
    have hh : (∅ : Set (World 0)).Nontrivial := h.mpr (pair_guard 0)
    simpa using hh
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@loses_mono) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.CompleteFailure.loses_mono.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.CompleteFailure.Mono.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p K => Loses p.2.1 K p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.CompleteFailure
    definition := none
    coordinates := #[0,1,4]
    readouts := #[{
      path := #["body","body","body","body","body","body","body"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Mono

namespace Finite
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature (ℕ × List Bool)
  (fun _ => Finset (World 3)) (fun _ => Prop)
def actual : Realization signature := realize signature
  (fun _ p T => Loses p.1 (T : Set (World 3)) p.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (T : Finset (World 3)) (v : List Bool),
    R.readout () (n,v) T ↔ MixedTripleExclusion.Losing n T v
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 0 {target 3 0, twin 3} []).mpr (by
    change 1 < ({target 3 0, twin 3} : Finset (World 3)).card
    simp [target_ne 3])
  exact hh
def family : Registration arena (type_of% @finite_losing_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_losing_iff, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(0, []), ∅, {target 3 0, twin 3}, ?_⟩
    intro h
    have hp : Loses 0 (({target 3 0, twin 3} : Finset (World 3)) : Set (World 3)) [] := by
      simpa [Loses, pair] using pair_guard 3
    have hh := h.mpr hp
    simpa [actual, realize, Loses] using hh
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_losing_iff) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.CompleteFailure.finite_losing_iff.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.CompleteFailure.Finite.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p T => Loses p.1 (T : Set (World 3)) p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.CompleteFailure
    definition := none
    coordinates := #[0,2]
    readouts := #[{
      path := #["body","body","body","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Finite

namespace Policy
abbrev Param := Σ d : ℕ, ℕ × List Bool
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Param
  (fun p => Policy p.1 × World p.1) (fun _ => Prop)
def actual : Realization signature := realize signature
  (fun _ p x => Identifies x.1 p.2.1 p.2.2 x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => True) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d n : ℕ} (K : Set (World d)) (v : List Bool) (h : History v),
    K ⊆ wholeSet v h → Loses n K v → ∀ P : Policy d,
      ¬ ∀ W ∈ K, R.readout () ⟨d,n,v⟩ (P,W)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let P : Policy 0 := fun _ _ => .inr (target 0 0)
  have hc : pair 0 ⊆ wholeSet [] (readings (target 0 0) []) := by
    intro W hW
    simp only [pair, Set.mem_insert_iff, Set.mem_singleton_iff] at hW
    rcases hW with rfl | rfl
    · rfl
    · ext i
      change Fin 1 at i
      fin_cases i
      norm_num [readings, readAt, target, twin, coeff, gain, acquisition,
        _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word, src, sourceChart,
        Matrix.trace, Fin.sum_univ_two]
  exact h (d := 0) (n := 0) (pair 0) [] _ hc (pair_guard 0) P (fun _ _ => True.intro)
def family : Registration arena (type_of% @loses_excludes_policy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@loses_excludes_policy, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    let P : Policy 0 := fun _ _ => .inr (target 0 0)
    refine ⟨⟨0,0,[]⟩, (P,target 0 0), (P,twin 0), ?_⟩
    intro h
    have hh : target 0 0 = twin 0 := Sum.inr.inj (h.mp rfl)
    exact target_ne 0 hh
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@loses_excludes_policy) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.CompleteFailure.loses_excludes_policy.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.CompleteFailure.Policy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p x => Identifies x.1 p.2.1 p.2.2 x.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.CompleteFailure
    definition := none
    coordinates := #[0,1,3,8]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","arg","body","body"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Policy
end Reg.D5.S3.Observer.CubicGain.CompleteFailure
