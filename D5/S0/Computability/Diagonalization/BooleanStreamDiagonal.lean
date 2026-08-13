/- GID: D5/S0/Computability/Diagonalization/BooleanStreamDiagonal
   generality: G
   mirror-B: D5/B/S0/Computability/Diagonalization/BooleanStreamDiagonal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Boolean diagonal negation exceeds every proposed enumeration of infinite streams. -/

import Mathlib.Computability.Partrec

namespace D5.S0.Computability.Diagonalization.BooleanStreamDiagonal

private theorem bool_not_has_no_fixed_point :
    ¬ ∃ b : Bool, Bool.not b = b := by
  decide

private theorem bool_streams_not_surjective (listing : Nat → Nat → Bool) :
    ¬ Function.Surjective listing := by
  intro hSurjective
  exact bool_not_has_no_fixed_point
    (Function.exists_fixed_point_of_surjective listing hSurjective Bool.not)

/-- For every proposed history-indexed listing of Boolean streams, diagonal negation gives
an explicit stream outside every row. Thus the listing does not exhaust the full stream space,
and no total evaluator indexed by natural program codes can output every Boolean trajectory. -/
theorem boolean_stream_diagonal_exceeds_every_history (P : Nat → Nat → Bool) :
    let D : Nat → Bool := fun h => Bool.not (P h h)
    (∀ h, D ≠ P h) ∧
      ¬ Function.Surjective P ∧
      ¬ ∃ V : Nat → Nat → Bool,
        Computable₂ V ∧
          ∀ trajectory : Nat → Bool,
            Computable trajectory → ∃ code, V code = trajectory := by
  dsimp only
  refine ⟨?_, bool_streams_not_surjective P, ?_⟩
  · intro h hEqual
    have hDiagonal := congrFun hEqual h
    simp at hDiagonal
  · intro hEvaluator
    obtain ⟨V, hVComputable, hVEnumerates⟩ := hEvaluator
    have hDiagonalComputable : Computable fun n => Bool.not (V n n) :=
      Primrec.not.to_comp.comp (hVComputable.comp Computable.id Computable.id)
    obtain ⟨e, he⟩ := hVEnumerates _ hDiagonalComputable
    have hDiagonal := congrFun he e
    simp at hDiagonal

example : Nat → Nat → Bool := fun _ _ => false

example : Nat := 0

end D5.S0.Computability.Diagonalization.BooleanStreamDiagonal
