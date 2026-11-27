/- GID: D5/S0/Automata/GuyotSquareRootStateComplexityRefutation
   generality: I
   mirror-B: D5/B/S0/Automata/GuyotSquareRootStateComplexityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Automata/GuyotSquareRootStateComplexityRefutation.claim; result=D5/S0/Automata/GuyotSquareRootStateComplexityRefutation.result; claim=D5/S0/Automata/GuyotSquareRootStateComplexityRefutation.claim
   digest: A length-twelve word refutes Guyot's complete DFA state bound. -/

import Mathlib.Computability.MyhillNerode
import OmegaBuild.Commands

compile_only_with_mathlib

/-!
# Guyot's square-root state bound

Mathematical scope: the universal upper-bound conjunct of Conjecture 1 in
*On state complexity for subword-closed languages*, arXiv:2407.10355v1, §2.2.
The equality involving the proposed extremizing word is a separate question.

The sole public theorem is the designated refutation result and is exempt
from four-slot escape registration under §3.9.
-/

/-
Public result:
  proof_shape: content
  escape_witness: separated (the finite prefix/suffix separation table);
    consumer: state_lower_bound, then result
admission_basis: open-problem-resolution (#34977; Refuted)
Direct frozen dependencies: none (pinned Mathlib only).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.GuyotSquareRootStateComplexityRefutation

/-- Words whose square is a scattered subsequence of the given word. -/
def squareRootLanguage {A : Type} (w : List A) : Language A :=
  {x | List.Sublist (x ++ x) w}

/-- The universal upper-bound conjunct of Guyot’s Conjecture 1. -/
def claim : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∀ (A : Type) [Finite A] (w : List A), w.length ≤ n →
      let c := (n + 2) / 3
      ∃ m : ℕ, m ≤ c ^ 2 - c + 3 ∧
        ∃ M : DFA A (Fin m), M.accepts = squareRootLanguage w

private def witness : List (Fin 4) := [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 3, 2]

private def prefixes (i : Fin 16) : List (Fin 4) :=
  #v[[], [0], [1], [2], [3], [0, 0], [0, 1], [0, 2], [0, 3],
     [1, 0], [1, 2], [1, 3], [2, 0], [2, 3], [3, 0], [1, 2, 3]].get i

private def suffixes (j : Fin 5) : List (Fin 4) :=
  #v[[], [0], [1], [2], [3]].get j

/-- Membership of a continuation in the left quotient for a selected prefix. -/
private def bit (i : Fin 16) (k : Fin 5) : Bool :=
  let x := prefixes i ++ suffixes k
  decide (List.Sublist (x ++ x) witness)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem separated :
    ∀ i j : Fin 16, i ≠ j → ∃ k : Fin 5, bit i k ≠ bit j k := by
  decide

private theorem state_lower_bound {m : ℕ} (M : DFA (Fin 4) (Fin m))
    (hM : M.accepts = squareRootLanguage witness) : 16 ≤ m := by
  have hinj : Function.Injective (M.eval ∘ prefixes) := by
    intro i j he
    change M.eval (prefixes i) = M.eval (prefixes j) at he
    by_contra hn
    obtain ⟨k, hk⟩ := separated i j hn
    have hq : Language.leftQuotient M.accepts (prefixes i) =
        Language.leftQuotient M.accepts (prefixes j) := by
      rw [Language.leftQuotient_accepts_apply, Language.leftQuotient_accepts_apply, he]
    rw [hM] at hq
    have hb := congrArg (fun L : Language (Fin 4) => suffixes k ∈ L) hq
    change List.Sublist ((prefixes i ++ suffixes k) ++ (prefixes i ++ suffixes k)) witness =
      List.Sublist ((prefixes j ++ suffixes k) ++ (prefixes j ++ suffixes k)) witness at hb
    apply hk
    exact Bool.eq_iff_iff.mpr (by simpa only [bit, decide_eq_true_eq] using Iff.of_eq hb)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hinj

/-- The four-letter word `abcdabcdabdc` needs at least sixteen states. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨m, hm, M, hM⟩ := h 12 (by decide) (Fin 4) witness (by decide)
  change m ≤ 15 at hm
  exact (by decide : ¬ (16 ≤ 15)) (le_trans (state_lower_bound M hM) hm)

end D5.S0.Automata.GuyotSquareRootStateComplexityRefutation
