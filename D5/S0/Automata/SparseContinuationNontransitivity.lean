/- GID: D5/S0/Automata/SparseContinuationNontransitivity
   generality: I
   mirror-B: D5/B/S0/Automata/SparseContinuationNontransitivity
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Automata/SparseContinuationNontransitivity.claim; result=D5/S0/Automata/SparseContinuationNontransitivity.result; claim=D5/S0/Automata/SparseContinuationNontransitivity.claim
   digest: The three-word promise xa,yb,za with outputs zero,zero,one has nontransitive common-legal-continuation compatibility. -/

import D5.S0.Automata.PromiseColoringTotalization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.SparseContinuationNontransitivity

open D5.S0.Automata.PromiseColoringTotalization

/-- The original five letters a,b,x,y,z are respectively 0,1,2,3,4 in Fin 5.
This is the actual finite promise {xa,yb,za}, coerced to the existing Set API. -/
def promise : Set (List (Fin 5)) :=
  ↑({[2, 0], [3, 1], [4, 0]} : Finset (List (Fin 5)))

/-- The prescribed output is one on za and zero on the other two legal words.
There is no output prescription on words outside the promise. -/
def output (word : promise) : Fin 2 :=
  if word.val = [4, 0] then 1 else 0

private def prefixX : Prefixes promise :=
  ⟨[2], ⟨[0], by simp [promise]⟩⟩

private def prefixY : Prefixes promise :=
  ⟨[3], ⟨[1], by simp [promise]⟩⟩

private def prefixZ : Prefixes promise :=
  ⟨[4], ⟨[0], by simp [promise]⟩⟩

/-- The transitivity assertion for common-legal-continuation compatibility on
this single promise. Its negation is the known original Proposition 3.3 example.
The existing Conflict excludes the diagonal, where output agreement is automatic. -/
def claim : Prop :=
  ∀ left middle right : Prefixes promise,
    (¬ Conflict promise output left middle) →
    (¬ Conflict promise output middle right) →
    ¬ Conflict promise output left right

/-- Construct the original sparse-continuation example inside the existing
word/promise model. This refutes claim, not the proposition asserting examples exist. -/
theorem result : ¬ claim := by
  intro transitive
  have first : ¬ Conflict promise output prefixX prefixY := by
    rintro ⟨_, suffix, hx, hy, _⟩
    have sx : suffix = [0] := by
      simpa [prefixX, promise] using hx
    have sy : suffix = [1] := by
      simpa [prefixY, promise] using hy
    exact (by decide : ([0] : List (Fin 5)) ≠ [1]) (sx.symm.trans sy)
  have second : ¬ Conflict promise output prefixY prefixZ := by
    rintro ⟨_, suffix, hy, hz, _⟩
    have sy : suffix = [1] := by
      simpa [prefixY, promise] using hy
    have sz : suffix = [0] := by
      simpa [prefixZ, promise] using hz
    exact (by decide : ([1] : List (Fin 5)) ≠ [0]) (sy.symm.trans sz)
  have third : Conflict promise output prefixX prefixZ := by
    refine ⟨?_, [0], ?_, ?_, ?_⟩
    · intro equal
      exact (by decide : ([2] : List (Fin 5)) ≠ [4])
        (congrArg (fun p : Prefixes promise => p.val) equal)
    · simp [prefixX, promise]
    · simp [prefixZ, promise]
    · simp [output, prefixX, prefixZ]
  exact (transitive prefixX prefixY prefixZ first second) third

#print axioms result

end D5.S0.Automata.SparseContinuationNontransitivity
