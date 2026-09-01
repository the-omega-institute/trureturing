/- GID: D5/S3/Observer/Completion/HistoryDecoderRepresentativeAsymmetry
   generality: G
   mirror-B: D5/B/S3/Observer/Completion/HistoryDecoderRepresentativeAsymmetry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A forgetful map can select fiber representatives without recovering every history. -/

import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-31):
   * Repository searches for left inverses, right inverses, noninjective
     projections, and fiber representatives found related frozen results, but
     no theorem joining the exact decoder obstruction with representative
     selection. In particular, `noninjective_layer_cannot_recover` concludes
     nonunique fiber-constant assignments rather than a right inverse.
   * Pinned Mathlib supplies `Function.LeftInverse.injective` and the exact
     supporting result `Function.Surjective.hasRightInverse`; both are applied
     below. It has no single theorem packaging the two source clauses.
   * The statement introduces no definition: the forgetful map, its witnessed
     nontrivial fiber, and realization of every scalar fiber are public inputs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Completion.HistoryDecoderRepresentativeAsymmetry

universe u v

/-- A witnessed nontrivial fiber prevents any decoder from recovering every
history. If every scalar state is realized, choice still provides one
representative in each scalar fiber. -/
theorem no_exact_history_decoder
    {Memory : Type u} {Scalar : Type v} (forget : Memory -> Scalar)
    (memoryEscape : exists first second : Memory,
      Not (first = second) /\ forget first = forget second)
    (scalarFibersRealized : Function.Surjective forget) :
    (Not (exists decoder : Scalar -> Memory,
      Function.LeftInverse decoder forget)) /\
      exists representative : Scalar -> Memory,
        Function.RightInverse representative forget := by
  constructor
  · rintro ⟨decoder, leftInverse⟩
    obtain ⟨first, second, distinct, sameScalar⟩ := memoryEscape
    exact distinct (leftInverse.injective sameScalar)
  · exact scalarFibersRealized.hasRightInverse

/- The premises are jointly satisfiable: first projection forgets the second
Boolean coordinate while realizing both scalar values. -/
example :
    let forget : Bool × Bool -> Bool := Prod.fst
    (Not (exists decoder : Bool -> Bool × Bool,
      Function.LeftInverse decoder forget)) /\
      exists representative : Bool -> Bool × Bool,
        Function.RightInverse representative forget := by
  dsimp only
  apply no_exact_history_decoder (fun state : Bool × Bool => state.1)
  · exact ⟨(false, false), (false, true), by decide, rfl⟩
  · intro scalar
    exact ⟨(scalar, false), rfl⟩

#print axioms no_exact_history_decoder

end D5.S3.Observer.Completion.HistoryDecoderRepresentativeAsymmetry
