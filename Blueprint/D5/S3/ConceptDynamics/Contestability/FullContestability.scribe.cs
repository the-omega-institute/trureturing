using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Contestability;

internal sealed class FullContestabilityDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Contestability/FullContestability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete contestability turns accepted statewise challenges into correct review, while "
            + "missing or observationally blind challenges expose precise obstructions.",
        H("Full Contestability and Correct Review"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("full-contestability-yields-correct-review"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "full_contestability_yields_correct_review"),
                H("Full contestability yields correct challenge-blind review"),
                StatementSource.FromAuthor(FullContestabilityReviewFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Complete contestability supplies an applicable and institutionally valid "
                            + "challenge at every erroneous state, with judgment equal to the "
                            + "state's target outcome. Choosing one such challenge at each error "
                            + "state produces a selector with all three guarantees.")),
                    Paragraph(Text(
                        "The selected challenge answers determine a challenge-blind reviewer on "
                            + "the error-state subtype. Whenever two error states have the same "
                            + "selected answer, the correctness of their selected challenges "
                            + "forces their target outcomes to agree, so the reviewer returns the "
                            + "target throughout that subtype."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("absent-challenge-and-blindness-prevent-review"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "absent_challenge_and_blindness_prevent_review"),
                H("Absent challenges and blindness prevent correct review"),
                StatementSource.FromAuthor(AbsentChallengeObstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose an erroneous state has no challenge that is simultaneously "
                            + "applicable, valid, and correct there. Then complete contestability "
                            + "fails, and any review output supported by an accepted challenge at "
                            + "that state must differ from its target.")),
                    Paragraph(Text(
                        "If every challenge also gives the same judgment at that state and at a "
                            + "second state with a different target, challenge blindness creates a "
                            + "global obstruction: no challenge-blind reviewer can equal the target "
                            + "on every state."))),
                DescribeRole.Proposition),
            Describe.Lean(
                DescribeId.Create("bool-identity-is-nontrivially-fully-contestable"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "bool_identity_is_nontrivially_fully_contestable"),
                H("The Boolean identity is nontrivially fully contestable"),
                StatementSource.FromAuthor(BooleanIdentityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Both Boolean states are declared erroneous, so the instance has a "
                            + "nonempty error population. At each state, choosing that state itself "
                            + "as the challenge satisfies the applicability equality, while "
                            + "validity holds automatically.")),
                    Paragraph(Text(
                        "The challenge judgment returns the chosen Boolean value and the target is "
                            + "the identity. The state-selected challenge therefore returns exactly "
                            + "the required outcome, giving a concrete nonvacuous instance of full "
                            + "contestability."))),
                DescribeRole.Lemma))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula AcceptedCorrectAt(
        Formula applicable,
        Formula valid,
        Formula judgment,
        Formula target,
        Formula challenge,
        Formula state) =>
        Seq(
            Apply(applicable, state, challenge), Sp, Land, Sp,
            Apply(valid, state, challenge), Sp, Land, Sp,
            Apply(judgment, challenge, state), Sp, Eq, Sp, Apply(target, state));

    private static Formula FullContestabilityReviewFormula()
    {
        Formula stateType = F.Id("State");
        Formula challengeType = F.Id("Challenge");
        Formula outcomeType = F.Id("Outcome");
        Formula proposition = F.Id("Prop");
        Formula erroneous = F.Id("Erroneous");
        Formula applicable = F.Id("Applicable");
        Formula valid = F.Id("Valid");
        Formula judgment = F.Id("judgment");
        Formula target = F.Id("target");
        Formula selected = F.Id("selected");
        Formula review = F.Id("review");
        Formula state = F.Id("x");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula errorStates = Call("ErrorState", stateType, erroneous);
        Formula selectedChallenge = Apply(selected, state);
        Formula selectionGuarantee = Seq(
            Forall, Sp, Typed(state, errorStates), Comma, Sp,
            AcceptedCorrectAt(
                applicable, valid, judgment, target, selectedChallenge, state));
        Formula reviewGuarantee = Seq(
            Call(
                "ChallengeBlind",
                Call("selectedChallengeAnswer", judgment, selected),
                review),
            Sp, Land, Sp,
            Grp(Seq(
                Forall, Sp, Typed(state, errorStates), Comma, Sp,
                Apply(review, state), Sp, Eq, Sp, Apply(target, state))));
        Formula conclusion = Seq(
            Exists, Sp, Typed(selected, Arrow(errorStates, challengeType)), Comma,
            RowBreak, Grp(),
            Grp(selectionGuarantee), Sp, Land, RowBreak, Grp(),
            Exists, Sp, Typed(review, Arrow(errorStates, outcomeType)), Comma,
            RowBreak, Grp(),
            reviewGuarantee);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            stateType, Comma, Sp, challengeType, Comma, Sp,
            outcomeType, Colon, Sp, type, Comma, RowBreak, Grp(),
            Typed(erroneous, Arrow(stateType, proposition)), Comma, RowBreak, Grp(),
            Typed(
                applicable,
                Arrow(stateType, Arrow(challengeType, proposition))),
            Comma, Sp,
            Typed(valid, Arrow(stateType, Arrow(challengeType, proposition))),
            Comma, RowBreak, Grp(),
            Typed(judgment, Arrow(challengeType, Arrow(stateType, outcomeType))),
            Comma, Sp,
            Typed(target, Arrow(stateType, outcomeType)), Comma, RowBreak, Grp(),
            Call(
                "FullyContestable",
                erroneous,
                applicable,
                valid,
                judgment,
                target),
            Sp, Rightarrow, RowBreak, Grp(),
            conclusion, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula AbsentChallengeObstructionFormula()
    {
        Formula stateType = F.Id("State");
        Formula challengeType = F.Id("Challenge");
        Formula outcomeType = F.Id("Outcome");
        Formula proposition = F.Id("Prop");
        Formula erroneous = F.Id("Erroneous");
        Formula applicable = F.Id("Applicable");
        Formula valid = F.Id("Valid");
        Formula judgment = F.Id("judgment");
        Formula target = F.Id("target");
        Formula first = F.Id("x");
        Formula second = F.Id("y");
        Formula challenge = F.Id("w");
        Formula review = F.Id("review");
        Formula state = F.Id("s");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula noAcceptedCorrectChallenge = Seq(
            Forall, Sp, Typed(challenge, challengeType), Comma, Sp,
            Neg, Sp, Grp(AcceptedCorrectAt(
                applicable, valid, judgment, target, challenge, first)));
        Formula sameAnswers = Seq(
            Forall, Sp, Typed(challenge, challengeType), Comma, Sp,
            Apply(judgment, challenge, first), Sp, Eq, Sp,
            Apply(judgment, challenge, second));
        Formula hypotheses = Seq(
            Apply(erroneous, first), Sp, Land, RowBreak, Grp(),
            Grp(noAcceptedCorrectChallenge), Sp, Land, RowBreak, Grp(),
            Grp(sameAnswers), Sp, Land, RowBreak, Grp(),
            Apply(target, first), Sp, Neq, Sp, Apply(target, second));
        Formula notFullyContestable = Seq(
            Neg, Sp,
            Call(
                "FullyContestable",
                erroneous,
                applicable,
                valid,
                judgment,
                target));
        Formula acceptedReviewFails = Seq(
            Forall, Sp, Typed(review, Arrow(stateType, outcomeType)), Comma, Sp,
            Call(
                "UsesAcceptedChallengeAt",
                applicable,
                valid,
                judgment,
                review,
                first),
            Sp, Rightarrow, Sp,
            Apply(review, first), Sp, Neq, Sp, Apply(target, first));
        Formula globallyCorrectBlindReview = Seq(
            Exists, Sp, Typed(review, Arrow(stateType, outcomeType)), Comma,
            RowBreak, Grp(),
            Call("ChallengeBlind", judgment, review), Sp, Land, Sp,
            Grp(Seq(
                Forall, Sp, Typed(state, stateType), Comma, Sp,
                Apply(review, state), Sp, Eq, Sp, Apply(target, state))));
        Formula conclusion = Seq(
            notFullyContestable, Sp, Land, RowBreak, Grp(),
            Grp(acceptedReviewFails), Sp, Land, RowBreak, Grp(),
            Neg, Sp, Grp(globallyCorrectBlindReview));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            stateType, Comma, Sp, challengeType, Comma, Sp,
            outcomeType, Colon, Sp, type, Comma, RowBreak, Grp(),
            Typed(erroneous, Arrow(stateType, proposition)), Comma, RowBreak, Grp(),
            Typed(
                applicable,
                Arrow(stateType, Arrow(challengeType, proposition))),
            Comma, Sp,
            Typed(valid, Arrow(stateType, Arrow(challengeType, proposition))),
            Comma, RowBreak, Grp(),
            Typed(judgment, Arrow(challengeType, Arrow(stateType, outcomeType))),
            Comma, Sp,
            Typed(target, Arrow(stateType, outcomeType)), Comma, RowBreak, Grp(),
            Typed(first, stateType), Comma, Sp, Typed(second, stateType), Comma,
            RowBreak, Grp(),
            Grp(hypotheses), Sp, Rightarrow, RowBreak, Grp(),
            conclusion, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula BooleanIdentityFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula truth = F.Id("True");
        Formula first = F.Id("x");
        Formula challenge = F.Id("w");
        Formula witness = F.Id("b");
        Formula nonempty = Seq(
            Exists, Sp, Typed(witness, boolean), Comma, Sp, truth);
        Formula allErroneous = Grp(
            first, Sp, Mapsto, Sp, truth);
        Formula equalityApplicable = Grp(
            Open, first, Comma, Sp, challenge, Close,
            Sp, Mapsto, Sp,
            challenge, Sp, Eq, Sp, first);
        Formula alwaysValid = Grp(
            Open, first, Comma, Sp, challenge, Close,
            Sp, Mapsto, Sp, truth);
        Formula challengeJudgment = Grp(
            Open, challenge, Comma, Sp, first, Close,
            Sp, Mapsto, Sp, challenge);
        Formula identityTarget = Grp(
            first, Sp, Mapsto, Sp, first);

        return Disp(Seq(
            Grp(nonempty), Sp, Land, RowBreak, Grp(),
            Call(
                "FullyContestable",
                allErroneous,
                equalityApplicable,
                alwaysValid,
                challengeJudgment,
                identityTarget),
            Dot));
    }
}
