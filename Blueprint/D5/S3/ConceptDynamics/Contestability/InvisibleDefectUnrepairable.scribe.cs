using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.D5.S3.ConceptDynamics.Contestability.InvisibleDefectUnrepairable;

internal sealed class InvisibleDefectUnrepairableDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Contestability/InvisibleDefectUnrepairable.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Challenge-indistinguishable states with different required outcomes defeat every "
            + "challenge-blind reviewer.",
        H("Invisible Defects Are Unrepairable by Blind Review"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("challenge-blind-review-cannot-separate"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "challenge_blind_review_cannot_separate"),
                H("Blind review cannot separate an invisible defect"),
                StatementSource.FromAuthor(SeparationImpossibilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Challenge blindness makes a reviewer constant on every class of states "
                            + "that gives identical answers to all available challenges.")),
                    Paragraph(Text(
                        "If two such states require different outcomes, universal correctness "
                            + "would identify both required outcomes through the common reviewed "
                            + "outcome. Their required difference therefore rules out every "
                            + "challenge-blind reviewer that is correct on all states.")),
                    Paragraph(Text(
                        "The obstruction is independent of finiteness, decidability, or any "
                            + "additional structure on states, challenges, responses, and outcomes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("correct-challenge-blind-review-exists-iff-coverage"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "correct_challenge_blind_review_exists_iff_coverage"),
                H("Coverage exactly characterizes correct blind review"),
                StatementSource.FromAuthor(CoverageCriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A fully correct challenge-blind reviewer exists exactly when the required "
                            + "outcome is constant on each fiber determined by all challenge answers.")),
                    Paragraph(Text(
                        "Necessity follows because blindness equates the reviewed outcomes of any "
                            + "answer-indistinguishable pair, while correctness transfers that "
                            + "equality to their requirements. For sufficiency, the required-outcome "
                            + "map itself is a reviewer, and the coverage condition makes it blind."))),
                DescribeRole.Proposition),
            Describe.Lean(
                DescribeId.Create("constant-unit-challenge-is-blind-to-bool-defect"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "constant_unit_challenge_is_blind_to_bool_defect"),
                H("A constant challenge misses a Boolean defect"),
                StatementSource.FromAuthor(ConstantChallengeWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The sole Unit-valued challenge returns the same Unit response for the "
                            + "Boolean states false and true, so those states are indistinguishable "
                            + "to any reviewer constrained by its answers.")),
                    Paragraph(Text(
                        "The identity target nevertheless assigns different required outcomes to "
                            + "the two states. This gives a concrete mixed fiber witnessing the "
                            + "general obstruction."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("constant-unit-challenge-cannot-review-bool"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "constant_unit_challenge_cannot_review_bool"),
                H("Constant challenges cannot implement the Boolean identity target"),
                StatementSource.FromAuthor(ConstantChallengeImpossibilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every reviewer blind to the constant Unit challenge must return one outcome "
                            + "for both Boolean states, whereas the identity target requires false "
                            + "and true respectively.")),
                    Paragraph(Text(
                        "Applying the general separation obstruction to this explicit pair proves "
                            + "that no such reviewer can be correct on every Boolean state."))),
                DescribeRole.Lemma))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula SameAnswers(
        Formula ask,
        Formula challenge,
        Formula challengeType,
        Formula first,
        Formula second) =>
        Seq(
            Forall, Sp, challenge, Colon, Sp, challengeType, Comma, Sp,
            Apply(ask, challenge, first), Sp, Eq, Sp, Apply(ask, challenge, second));

    private static Formula CorrectOnAllStates(
        Formula review,
        Formula required,
        Formula state,
        Formula stateType) =>
        Seq(
            Forall, Sp, state, Colon, Sp, stateType, Comma, Sp,
            Apply(review, state), Sp, Eq, Sp, Apply(required, state));

    private static Formula ReviewerExists(
        Formula ask,
        Formula required,
        Formula review,
        Formula state,
        Formula stateType,
        Formula outcomeType) =>
        Seq(
            Exists, Sp, Typed(review, Arrow(stateType, outcomeType)), Comma, RowBreak, Grp(),
            Call("ChallengeBlind", ask, review), Sp, Land, Sp,
            Grp(CorrectOnAllStates(review, required, state, stateType)));

    private static Formula SeparationImpossibilityFormula()
    {
        Formula stateType = F.Id("State");
        Formula challengeType = F.Id("Challenge");
        Formula responseType = F.Id("Response");
        Formula outcomeType = F.Id("Outcome");
        Formula ask = F.Id("ask");
        Formula required = F.Id("required");
        Formula review = F.Id("review");
        Formula state = F.Id("s");
        Formula challenge = F.Id("c");
        Formula first = F.Id("x");
        Formula second = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula sameAnswers = SameAnswers(
            ask, challenge, challengeType, first, second);
        Formula differentRequirements = Seq(
            Apply(required, first), Sp, Neq, Sp, Apply(required, second));
        Formula obstruction = ReviewerExists(
            ask, required, review, state, stateType, outcomeType);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            stateType, Comma, Sp, challengeType, Comma, Sp,
            responseType, Comma, Sp, outcomeType, Colon, Sp, type, Comma, RowBreak, Grp(),
            Typed(ask, Arrow(challengeType, Arrow(stateType, responseType))), Comma, Sp,
            Typed(required, Arrow(stateType, outcomeType)), Comma, RowBreak, Grp(),
            Typed(first, stateType), Comma, Sp, Typed(second, stateType), Comma, RowBreak, Grp(),
            Open, sameAnswers, Sp, Land, Sp, differentRequirements, Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Neg, Sp, Open, obstruction, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula CoverageCriterionFormula()
    {
        Formula stateType = F.Id("State");
        Formula challengeType = F.Id("Challenge");
        Formula responseType = F.Id("Response");
        Formula outcomeType = F.Id("Outcome");
        Formula ask = F.Id("ask");
        Formula required = F.Id("required");
        Formula review = F.Id("review");
        Formula state = F.Id("s");
        Formula otherState = F.Id("t");
        Formula boundState = F.Id("u");
        Formula challenge = F.Id("c");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula reviewerExists = ReviewerExists(
            ask, required, review, boundState, stateType, outcomeType);
        Formula coverage = Seq(
            Forall, Sp, state, Comma, Sp, otherState, Colon, Sp, stateType, Comma, RowBreak,
            Grp(),
            Grp(SameAnswers(ask, challenge, challengeType, state, otherState)),
            Sp, Rightarrow, Sp,
            Apply(required, state), Sp, Eq, Sp, Apply(required, otherState));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            stateType, Comma, Sp, challengeType, Comma, Sp,
            responseType, Comma, Sp, outcomeType, Colon, Sp, type, Comma, RowBreak, Grp(),
            Typed(ask, Arrow(challengeType, Arrow(stateType, responseType))), Comma, Sp,
            Typed(required, Arrow(stateType, outcomeType)), Comma, RowBreak, Grp(),
            Open, reviewerExists, Close, Sp, Iff, RowBreak, Grp(),
            coverage, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ConstantChallengeWitnessFormula()
    {
        Formula challenge = F.Id("c");
        Formula unit = F.Id("Unit");
        Formula falseState = F.Id("false");
        Formula trueState = F.Id("true");
        Formula identity = F.Id("id");
        Formula sameAnswers = Seq(
            Forall, Sp, challenge, Colon, Sp, unit, Comma, Sp,
            Call("constantUnit", challenge, falseState), Sp, Eq, Sp,
            Call("constantUnit", challenge, trueState));
        Formula differentTargets = Seq(
            Apply(identity, falseState), Sp, Neq, Sp, Apply(identity, trueState));

        return Disp(Seq(
            Open, sameAnswers, Close, Sp, Land, RowBreak, Grp(),
            differentTargets, Dot));
    }

    private static Formula ConstantChallengeImpossibilityFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula review = F.Id("review");
        Formula state = F.Id("state");
        Formula constantChallenge = F.Id("constantUnit");
        Formula identity = F.Id("id");
        Formula correctness = Seq(
            Forall, Sp, state, Colon, Sp, boolean, Comma, Sp,
            Apply(review, state), Sp, Eq, Sp, Apply(identity, state));
        Formula reviewerExists = Seq(
            Exists, Sp, Typed(review, Arrow(boolean, boolean)), Comma, RowBreak, Grp(),
            Call("ChallengeBlind", constantChallenge, review), Sp, Land, Sp,
            Grp(correctness));

        return Disp(Seq(
            Neg, Sp, Open, reviewerExists, Close, Dot));
    }
}
