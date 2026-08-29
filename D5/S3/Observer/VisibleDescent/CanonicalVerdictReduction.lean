/- GID: D5/S3/Observer/VisibleDescent/CanonicalVerdictReduction
   generality: G
   mirror-B: D5/B/S3/Observer/VisibleDescent/CanonicalVerdictReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Verdict tables descend, reduce by column representatives, and split after extension. -/

import D5.S0.Naming.VerdictColumnSeparation
import D5.S3.Observer.Refinement.DoubleExtensionalEvaluationDescent

/- Search audit (2026-08-29):
   * Current-tree name and body-shape searches found the canonical double quotient in
     `DoubleExtensionalEvaluationDescent` and the extension witness in
     `VerdictColumnSeparation`; both are imported rather than restated as definitions.
   * Searches for lossless inclusion-minimal test subsets and unique verdict-column
     representatives found no D5 theorem or pinned-Mathlib theorem with the source shape.
   * Pinned Mathlib supplies `Setoid.ker` and the set operations used in the minimality proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.VisibleDescent.CanonicalVerdictReduction

open D5.S0.Naming.VerdictColumnSeparation
open D5.S3.Observer.Refinement.DoubleExtensionalEvaluationDescent

/-- A Boolean verdict table has a canonical double extensional quotient. A test subset is
lossless and inclusion-minimal exactly when it selects one representative from every verdict
column, and adjoining one implementation can split two distinct columns that agreed on the
original population. -/
theorem canonical_verdict_reduction
    {Implementation Test : Type*} (verdict : Implementation -> Test -> Bool) :
    let implementationKernel : Setoid Implementation :=
      Setoid.ker (fun implementation => fun test => verdict implementation test)
    let testKernel : Setoid Test :=
      Setoid.ker (fun test => fun implementation => verdict implementation test)
    let canonicalVerdict :
        Quotient implementationKernel -> Quotient testKernel -> Bool :=
      fun implementationClass testClass =>
        Quotient.liftOn₂ implementationClass testClass verdict
          (fun firstImplementation firstTest secondImplementation secondTest sameRow sameColumn =>
            (show verdict firstImplementation firstTest =
                verdict secondImplementation firstTest from
              congrFun sameRow firstTest).trans
              (show verdict secondImplementation firstTest =
                  verdict secondImplementation secondTest from
                congrFun sameColumn secondImplementation))
    ((forall (firstImplementation secondImplementation : Implementation)
        (firstTest secondTest : Test),
        implementationKernel firstImplementation secondImplementation ->
          testKernel firstTest secondTest ->
          verdict firstImplementation firstTest =
            verdict secondImplementation secondTest) /\
      (forall (implementation : Implementation) (test : Test),
        canonicalVerdict (Quotient.mk' implementation) (Quotient.mk' test) =
          verdict implementation test) /\
      (forall other : Quotient implementationKernel -> Quotient testKernel -> Bool,
        (forall (implementation : Implementation) (test : Test),
          other (Quotient.mk' implementation) (Quotient.mk' test) =
            verdict implementation test) ->
        other = canonicalVerdict)) /\
    (forall kept : Set Test,
      (((forall test, exists representative,
          representative ∈ kept /\ testKernel representative test) /\
        (forall candidate : Set Test, candidate ⊆ kept ->
          (forall test, exists representative,
            representative ∈ candidate /\ testKernel representative test) ->
          kept ⊆ candidate)) <->
        (forall test, ExistsUnique fun representative =>
          representative ∈ kept /\ testKernel representative test))) /\
    (forall {firstTest secondTest : Test}, firstTest ≠ secondTest ->
      testKernel firstTest secondTest ->
      exists extended : Option Implementation -> Test -> Bool,
        (forall implementation, extended (some implementation) = verdict implementation) /\
          extended none firstTest ≠ extended none secondTest) := by
  dsimp only
  constructor
  · exact double_extensional_evaluation_descent verdict
  constructor
  · intro kept
    constructor
    · rintro ⟨lossless, minimal⟩ test
      obtain ⟨representative, representativeKept, representativeRelated⟩ := lossless test
      refine ⟨representative, ⟨representativeKept, representativeRelated⟩, ?_⟩
      intro other ⟨otherKept, otherRelated⟩
      by_contra distinct
      let candidate : Set Test := kept \ {other}
      have candidateSubset : candidate ⊆ kept := by
        intro member memberCandidate
        exact memberCandidate.1
      have candidateLossless : forall target, exists member,
          member ∈ candidate /\
            Setoid.ker (fun test => fun implementation => verdict implementation test)
              member target := by
        intro target
        obtain ⟨member, memberKept, memberRelated⟩ := lossless target
        by_cases memberOther : member = other
        · subst member
          refine ⟨representative, ?_, ?_⟩
          · exact ⟨representativeKept, by simpa using Ne.symm distinct⟩
          · exact representativeRelated.trans (otherRelated.symm.trans memberRelated)
        · exact ⟨member, ⟨memberKept, memberOther⟩, memberRelated⟩
      have everyKeptIsCandidate : kept ⊆ candidate :=
        minimal candidate candidateSubset candidateLossless
      have otherCandidate : other ∈ candidate := everyKeptIsCandidate otherKept
      exact otherCandidate.2 rfl
    · intro uniqueRepresentatives
      constructor
      · intro test
        obtain ⟨representative, representativeProperty, _⟩ := uniqueRepresentatives test
        exact ⟨representative, representativeProperty⟩
      · intro candidate candidateSubset candidateLossless
        intro keptTest keptTestKept
        obtain ⟨candidateTest, candidateTestMember, candidateTestRelated⟩ :=
          candidateLossless keptTest
        obtain ⟨representative, representativeProperty, representativeUnique⟩ :=
          uniqueRepresentatives keptTest
        have candidateEqualsRepresentative : candidateTest = representative :=
          representativeUnique candidateTest
            ⟨candidateSubset candidateTestMember, candidateTestRelated⟩
        have keptEqualsRepresentative : keptTest = representative :=
          representativeUnique keptTest
            ⟨keptTestKept,
              (Setoid.ker
                (fun test => fun implementation => verdict implementation test)).refl keptTest⟩
        have candidateEqualsKept : candidateTest = keptTest :=
          candidateEqualsRepresentative.trans keptEqualsRepresentative.symm
        simpa [candidateEqualsKept] using candidateTestMember
  · intro firstTest secondTest distinctTests sameColumn
    apply verdict_columns_can_split verdict distinctTests
    intro implementation
    exact congrFun sameColumn implementation

#print axioms canonical_verdict_reduction

end D5.S3.Observer.VisibleDescent.CanonicalVerdictReduction
