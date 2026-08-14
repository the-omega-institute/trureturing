/- GID: D5/S0/Computability/Searchability/SearchableWindowDecision
   generality: G
   mirror-B: D5/B/S0/Computability/Searchability/SearchableWindowDecision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A searchable input window gives a Boolean decision for every decidable universal test. -/

import Mathlib.Data.Bool.Basic

namespace D5.S0.Computability.Searchability.SearchableWindowDecision

/-- A selector for Boolean queries decides a universal Boolean property by
searching for a counterexample. -/
theorem searchable_window_forall_decidable
    {Input Output : Type*}
    (domain : Input -> Prop)
    (select : (Input -> Bool) -> Input)
    (select_mem : forall query : Input -> Bool, domain (select query))
    (select_true_of_exists : forall query : Input -> Bool,
      (exists z, domain z /\ query z = true) -> query (select query) = true)
    (sut : Input -> Output)
    (test : Output -> Bool) :
    let counterexample : Input -> Bool := fun z => !(test (sut z))
    let verdict : Bool := test (sut (select counterexample))
    verdict = true <-> forall z, domain z -> test (sut z) = true := by
  dsimp only
  constructor
  · intro hvis z hz
    by_contra htest
    have hfalse : test (sut z) = false :=
      Bool.eq_false_of_not_eq_true htest
    have hselectedCounterexample :
        (!(test (sut (select fun x => !(test (sut x)))))) = true :=
      select_true_of_exists (fun x => !(test (sut x)))
        ⟨z, hz, by simp [hfalse]⟩
    have hselectedFalse :
        test (sut (select fun x => !(test (sut x)))) = false := by
      simpa using hselectedCounterexample
    have hcontradiction : (false : Bool) = true :=
      hselectedFalse.symm.trans hvis
    cases hcontradiction
  · intro hall
    exact hall _ (select_mem _)

/-- The input type used by the satisfiability witness is inhabited. -/
example : Unit := ()

/-- The selector premises are jointly satisfiable on a one-point window. -/
example :
    let domain : Unit -> Prop := fun _ => True
    let select : (Unit -> Bool) -> Unit := fun _ => ()
    (forall query : Unit -> Bool, domain (select query)) /\
      forall query : Unit -> Bool, (exists z, domain z /\ query z = true) ->
        query (select query) = true := by
  dsimp only
  constructor
  · intro query
    trivial
  · intro query hquery
    obtain ⟨z, hz, htrue⟩ := hquery
    cases z
    exact htrue

end D5.S0.Computability.Searchability.SearchableWindowDecision
