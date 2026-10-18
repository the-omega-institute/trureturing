import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Automata.TwoStateShortWordSampleBound
import Reg.Support.DependentFamily

/-! The alphabet-size successor in the sample cutoff is a source-bound observation. -/

namespace Reg.D5.S0.Automata.TwoStateShortWordSampleBound

open _root_.D5.S0.Automata.DFAOStateLowerBound
open _root_.D5.S0.Automata.FiniteSampleRestriction
open _root_.D5.S0.Automata.TwoStateShortWordSampleBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature
  Law R := ∃ C : ℕ, ∀ (k : ℕ) (D : Finset (List (Fin k)))
    (target : {word : List (Fin k) // word ∈ D} → Bool),
    (∀ word ∈ D, (word : List (Fin k)).length ≤ 2) →
    (∀ E : Finset {word : List (Fin k) // word ∈ D}, E.card ≤ C * R.readout () () k →
      ∃ (State : Type) (_ : Fintype State) (machine : DFAO (Fin k) Bool State),
        Fintype.card State ≤ 2 ∧ FitsSubsample machine Subtype.val target (fun i : E => i.val)) →
    ∃ (State : Type) (_ : Fintype State) (machine : DFAO (Fin k) Bool State),
      Fintype.card State ≤ 2 ∧ CorrectOnFamily machine Subtype.val target

def actual : Realization signature :=
  realize signature (fun _ _ n => n + 1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem actual_bridge : (type_of% alphabet_linear_sample_bound) ↔ arena.Law actual :=
  Iff.rfl

theorem rejected_law : ¬ arena.Law rejected := by
  classical
  rintro ⟨C, h⟩
  let a : Fin 1 := 0
  let D : Finset (List (Fin 1)) := {[], [a], [a,a]}
  let target : {word : List (Fin 1) // word ∈ D} → Bool :=
    fun i => decide (i.val.length = 2)
  have localModels : ∀ E : Finset {word : List (Fin 1) // word ∈ D},
      E.card ≤ C * rejected.readout () () 1 →
      ∃ (State : Type) (_ : Fintype State) (machine : DFAO (Fin 1) Bool State),
        Fintype.card State ≤ 2 ∧ FitsSubsample machine Subtype.val target (fun i : E => i.val) := by
    intro E hE
    have he : E = ∅ := Finset.card_eq_zero.mp (by simpa [rejected, realize] using hE)
    subst E
    let machine : DFAO (Fin 1) Bool Unit :=
      {start := (), step := fun _ _ => (), output := fun _ => false, accept := ∅}
    refine ⟨Unit, inferInstance, machine, by simp, ?_⟩
    intro i
    exact (Finset.notMem_empty _ i.property).elim
  have hlen : ∀ word ∈ D, (word : List (Fin 1)).length ≤ 2 := by
    simp only [D, Finset.mem_insert, Finset.mem_singleton]
    rintro word (rfl | rfl | rfl) <;> simp
  obtain ⟨State, inst, machine, bound, correct⟩ := h 1 D target hlen localModels
  letI := inst
  have hzero : machine.output machine.start = false := by
    simpa [target, DFAO.evalOutput, DFA.eval, DFA.evalFrom] using
      correct ⟨[], by simp [D]⟩
  have hone : machine.output (machine.step machine.start a) = false := by
    simpa [target, DFAO.evalOutput, DFA.eval, DFA.evalFrom] using
      correct ⟨[a], by simp [D]⟩
  have htwo : machine.output (machine.step (machine.step machine.start a) a) = true := by
    simpa [target, DFAO.evalOutput, DFA.eval, DFA.evalFrom] using
      correct ⟨[a,a], by simp [D]⟩
  have hzeroTwo : machine.start ≠ machine.step (machine.step machine.start a) a := by
    intro he
    have hh := congrArg machine.output he
    simp only [hzero, htwo] at hh
    cases hh
  have honeTwo : machine.step machine.start a ≠ machine.step (machine.step machine.start a) a := by
    intro he
    have hh := congrArg machine.output he
    simp only [hone, htwo] at hh
    cases hh
  have hzeroOne : machine.start = machine.step machine.start a := by
    by_contra hn
    have hc : ({machine.start, machine.step machine.start a,
        machine.step (machine.step machine.start a) a} : Finset State).card = 3 := by
      simp [hn, hzeroTwo, honeTwo]
    have hb := Finset.card_le_univ
      ({machine.start, machine.step machine.start a,
        machine.step (machine.step machine.start a) a} : Finset State)
    omega
  exact honeTwo (congrArg (fun q => machine.step q a) hzeroOne)

def registration : Registration arena (type_of% alphabet_linear_sample_bound) where
  actual := actual
  bridge := actual_bridge
  variation := ⟨actual_bridge.mp alphabet_linear_sample_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), (0 : ℕ), (3 : ℕ), by change (0 : ℕ) + 1 ≠ 3 + 1; decide⟩

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@alphabet_linear_sample_bound)
    (type_of% (realize signature (fun _ _ n => n + 1) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S0.Automata.TwoStateShortWordSampleBound.alphabet_linear_sample_bound.__information_unit,
  realizationName := `Reg.D5.S0.Automata.TwoStateShortWordSampleBound.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ n => n + 1) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Automata.TwoStateShortWordSampleBound,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["arg", "body", "body", "body", "body", "body",
        "domain", "body", "domain", "arg", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["fn", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration

end Reg.D5.S0.Automata.TwoStateShortWordSampleBound
