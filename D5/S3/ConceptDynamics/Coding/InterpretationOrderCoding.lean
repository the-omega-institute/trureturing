/- GID: D5/S3/ConceptDynamics/Coding/InterpretationOrderCoding
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/InterpretationOrderCoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Any chosen finite interpretation can receive the unique shortest prefix codeword. -/

import D5.S0.Computability.Coding.PrefixFreeCode

/-!
# Coding-dependent orders on finite interpretations

## Library-search receipt (2026-08-21)

* Repository command (recorded without reflow):
  `rg -n -i "prefix code|prefix-free|prefixfree|IsPrefix|strict.*short|shortest.*code|编码依赖|前缀编码" D5 -g '*.lean'`.
  It found the exact repository predicate
  `D5.S0.Computability.Coding.PrefixFreeCode.IsPrefixFree`, imported and used below.
  `KraftConverse.exists_isPrefixFree_code_of_kraft` is adjacent but returns an unlabelled list
  of codewords, so it does not select a chosen interpretation.
* Pinned-Mathlib command (recorded without reflow):
  `rg -n "def IsPrefix|theorem .*IsPrefix|namespace.*Prefix|PrefixFree|prefix code|prefix-free|IsAntichain.*List" .lake/packages/mathlib/Mathlib -g '*.lean'`.
  It found the list prefix relation and its lemmas but no prefix-code predicate or theorem
  assigning the unique shortest word to a chosen member.
* The construction below therefore reuses the repository predicate and core
  `List.IsPrefix.length_le` / `List.IsPrefix.eq_of_length`; it proves only the missing labelled
  two-length construction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.InterpretationOrderCoding

open D5.S0.Computability.Coding.PrefixFreeCode

/-- For a finite indexed family of interpretations and any chosen member, an unrestricted
coding alphabet admits an injective prefix code in which that member has a strictly shorter
codeword than every other member. Thus shortest-code ordering alone depends on the coding
language; objectivity requires an independently restricted class of languages. -/
theorem exists_prefix_code_with_chosen_unique_shortest
    {n : Nat} (chosen : Fin n) :
    ∃ code : Fin n -> List (Bool × Fin n),
      Function.Injective code ∧
      IsPrefixFree (Set.range code) ∧
      ∀ other, other ≠ chosen -> (code chosen).length < (code other).length := by
  let code : Fin n -> List (Bool × Fin n) := fun p =>
    if p = chosen then [(false, chosen)] else [(true, chosen), (false, p)]
  refine ⟨code, ?_, ?_, ?_⟩
  · intro p q hpq
    by_cases hp : p = chosen
    · subst p
      by_cases hq : q = chosen
      · exact hq.symm
      · simp [code, hq] at hpq
    · by_cases hq : q = chosen
      · subst q
        simp [code, hp] at hpq
      · simpa [code, hp, hq] using hpq
  · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hpq
    by_cases hp : p = chosen
    · subst p
      by_cases hq : q = chosen
      · simp [code, hq]
      · simp [code, hq] at hpq
    · by_cases hq : q = chosen
      · subst q
        exfalso
        have hlength := hpq.length_le
        simp [code, hp] at hlength
      · exact hpq.eq_of_length (by simp [code, hp, hq])
  · intro other hother
    simp [code, hother]

/-- The public hypotheses are inhabited by a family of two interpretations. -/
example :
    ∃ code : Fin 2 -> List (Bool × Fin 2),
      Function.Injective code ∧
      IsPrefixFree (Set.range code) ∧
      ∀ other, other ≠ (0 : Fin 2) -> (code 0).length < (code other).length :=
  exists_prefix_code_with_chosen_unique_shortest 0

#print axioms exists_prefix_code_with_chosen_unique_shortest

end D5.S3.ConceptDynamics.Coding.InterpretationOrderCoding
