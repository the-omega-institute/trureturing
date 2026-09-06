/- GID: D5/S0/Automata/BinaryZeckendorfLanguage
   generality: G
   mirror-B: D5/B/S0/Automata/BinaryZeckendorfLanguage
   mirror-E: none(waiver:language-characterization)
   anchors: [mathlib/module/Mathlib.Data.List.Chain]
   digest: Successful binary base execution is equivalent to nonadjacency. -/

import D5.S0.Automata.TypedPartialDFAOOverBase
import Mathlib.Data.List.Chain
import Mathlib.Tactic.FinCases

/-! # Exact Binary Zeckendorf Language

Successful base words are exactly the words with no adjacent ones, including
the empty word and arbitrary leading-zero padding. This identifies the precise
language of the paper's typed base and supplies the structural premise for the
arithmetic input-legality bridge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.BinaryZeckendorfLanguage

open D5.S0.Automata.TypedPartialDFAOOverBase

/-- Each adjacent pair contains a zero; empty and zero-padded words are allowed. -/
def NoAdjacentOnes (word : List (Fin 2)) : Prop :=
  word.IsChain (fun a b => a = 0 ∨ b = 0)

/-- Successful execution remembers the preceding bit in its initial base state. -/
theorem base_success_iff_chain (previous : Fin 2) (word : List (Fin 2)) :
    (∃ state, binaryZeckendorfBase.evalFrom
      (if previous = 0 then .previousZero else .previousOne) word = some state) ↔
      (previous :: word).IsChain (fun a b => a = 0 ∨ b = 0) := by
  induction word generalizing previous with
  | nil => simp [PartialDFA.evalFrom, runTransition]
  | cons a word ih =>
    fin_cases previous <;> fin_cases a <;>
      simp [List.isChain_cons_cons, PartialDFA.evalFrom, runTransition,
        binaryZeckendorfBase] at ih ⊢ <;> aesop

/-- The base's successful language is exactly the no-adjacent-ones language. -/
theorem base_success_iff_noAdjacentOnes (word : List (Fin 2)) :
    (∃ state, binaryZeckendorfBase.eval word = some state) ↔ NoAdjacentOnes word := by
  have h := base_success_iff_chain 0 word
  cases word <;>
    simpa [NoAdjacentOnes, PartialDFA.eval, binaryZeckendorfBase,
      List.isChain_cons_cons] using h

end D5.S0.Automata.BinaryZeckendorfLanguage
