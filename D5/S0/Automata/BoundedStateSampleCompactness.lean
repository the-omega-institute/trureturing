/- GID: D5/S0/Automata/BoundedStateSampleCompactness
   generality: G
   mirror-B: D5/B/S0/Automata/BoundedStateSampleCompactness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite samples characterize bounded-state output automata. -/

import D5.S0.Automata.FiniteSampleRestriction
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.BoundedStateSampleCompactness

open D5.S0.Automata.DFAOStateLowerBound
open D5.S0.Automata.FiniteSampleRestriction

universe u v w

/-- Bounded-state realizability is compact for finite input and output alphabets.
The domain carries its own target labels; no output is prescribed outside it.
The statement also includes empty domains and zero state budgets. -/
theorem bounded_state_sample_compactness
    {Alphabet : Type u} {Output : Type v} [Finite Alphabet] [Finite Output]
    (D : Set (List Alphabet)) (target : D → Output) (s : ℕ) :
    (∃ (State : Type w) (_ : Fintype State) (machine : DFAO Alphabet Output State),
      Fintype.card State ≤ s ∧ CorrectOnFamily machine Subtype.val target) ↔
    ∀ E : Finset D,
      ∃ (State : Type w) (_ : Fintype State) (machine : DFAO Alphabet Output State),
        Fintype.card State ≤ s ∧
          FitsSubsample machine Subtype.val target (fun i : E => i.val) := by
  classical
  let := Fintype.ofFinite Alphabet
  let := Fintype.ofFinite Output
  constructor
  · rintro ⟨State, inst, machine, bound, correct⟩ E
    exact ⟨State, inst, machine, bound,
      fitsSubsample_of_correctOnFamily machine Subtype.val target
        (fun i : E => i.val) correct⟩
  · intro localModels
    let Table := Fin s × (Fin s → Alphabet → Fin s) × (Fin s → Output)
    let machineOf : Table → DFAO Alphabet Output (Fin s) := fun t =>
      { start := t.1, step := t.2.1, output := t.2.2, accept := ∅ }
    have tableCard : Fintype.card Table =
        s * s ^ (s * Fintype.card Alphabet) * Fintype.card Output ^ s := by
      simp only [Table, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
        ← pow_mul, mul_comm, mul_assoc]
    let enumeration := Fintype.equivFinOfCardEq tableCard
    have pad : ∀ (State : Type w) [Fintype State]
        (machine : DFAO Alphabet Output State), Fintype.card State ≤ s →
        ∃ t : Table, ∀ word, (machineOf t).evalOutput word = machine.evalOutput word := by
      intro State inst machine bound
      let embed : State → Fin s := fun q => (Fintype.equivFin State q).castLE bound
      have injective : Function.Injective embed := by
        intro p q h
        apply (Fintype.equivFin State).injective
        exact Fin.ext (congrArg (fun x : Fin s => x.val) h)
      let : Nonempty State := ⟨machine.start⟩
      let retract : Fin s → State := Function.invFun embed
      have retract_embed : ∀ q, retract (embed q) = q :=
        Function.leftInverse_invFun injective
      let t : Table := ⟨embed machine.start,
        (fun q a => embed (machine.step (retract q) a)),
        (fun q => machine.output (retract q))⟩
      have run : ∀ (word : List Alphabet) (q : State),
          (machineOf t).toDFA.evalFrom (embed q) word =
            embed (machine.toDFA.evalFrom q word) := by
        intro word
        induction word with
        | nil => intro q; rfl
        | cons a tail ih =>
          intro q
          simp only [DFA.evalFrom_cons]
          change (machineOf t).toDFA.evalFrom
            (embed (machine.step (retract (embed q)) a)) tail = _
          rw [retract_embed, ih]
      refine ⟨t, ?_⟩
      intro word
      change machine.output (retract
        ((machineOf t).toDFA.evalFrom (embed machine.start) word)) = _
      rw [run, retract_embed]
      rfl
    have globalTable : ∃ t : Table, CorrectOnFamily (machineOf t) Subtype.val target := by
      by_contra absent
      have failure : ∀ t : Table, ∃ i : D,
          (machineOf t).evalOutput i.val ≠ target i := by
        intro t
        by_contra noFailure
        apply absent
        exact ⟨t, fun i => by simpa using not_exists.mp noFailure i⟩
      choose badWord bad using failure
      let E : Finset D := Finset.univ.image (badWord ∘ enumeration.symm)
      obtain ⟨State, inst, machine, bound, fits⟩ := localModels E
      obtain ⟨t, agrees⟩ := pad State machine bound
      have member : badWord t ∈ E := by
        apply Finset.mem_image.mpr
        exact ⟨enumeration t, Finset.mem_univ _, by simp⟩
      exact bad t ((agrees _).trans (fits ⟨badWord t, member⟩))
    obtain ⟨t, correct⟩ := globalTable
    let e : Fin s ≃ ULift.{w} (Fin s) := Equiv.ulift.symm
    let machine : DFAO Alphabet Output (ULift.{w} (Fin s)) :=
      { toDFA := DFA.reindex e (machineOf t).toDFA
        output := fun q => (machineOf t).output (e.symm q) }
    refine ⟨ULift.{w} (Fin s), inferInstance, machine, by simp, ?_⟩
    intro i
    change (machineOf t).output
      (e.symm ((DFA.reindex e (machineOf t).toDFA).eval i.val)) = target i
    rw [DFA.eval_reindex, e.symm_apply_apply]
    exact correct i

#print axioms bounded_state_sample_compactness

end D5.S0.Automata.BoundedStateSampleCompactness
