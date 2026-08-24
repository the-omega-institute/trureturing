using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class ExperimentStatePosteriorDecisionSeparationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical experiment-law quotient is a state-side object, while the "
            + "target posterior is an evidence-side sufficient input for Bayes decisions.",
        H("Experiment State and Posterior Decision Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("experiment-state-and-posterior-decision-separate"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DecisionRisk/"
                        + "ExperimentStatePosteriorDecisionSeparation."
                        + "experiment_state_and_posterior_decision_separation"),
                H("Experiment state and posterior decision separate"),
                StatementSource.FromAuthor(SeparationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A complete experiment law is a function from source states to law "
                            + "values. Quotienting the source by equality of those values "
                            + "constructs the canonical experiment state. Mathlib's kernel "
                            + "lift is injective on this quotient and composes with the "
                            + "canonical class map to recover the original law exactly.")),
                    Paragraph(Text(
                        "On the evidence side, a finite nonnegative joint target-evidence "
                            + "weight constructs the target posterior by normalization. If "
                            + "two evidence values have the same posterior, every fixed real "
                            + "loss family gives the same normalized conditional risk at "
                            + "each action.")),
                    Paragraph(Text(
                        "Consequently equal posteriors determine both the conditional Bayes "
                            + "value and the full set of Bayes-optimal actions, for every "
                            + "action carrier. The state quotient and posterior are not "
                            + "identified: their public constructions have different source "
                            + "domains, states for the former and evidence for the latter."))),
                DescribeRole.Theorem))));

    private static Formula SeparationFormula()
    {
        Formula state = F.Id("X");
        Formula lawType = F.Id("Law");
        Formula parameter = Theta;
        Formula evidenceType = F.Id("E");
        Formula law = Lambda;
        Formula joint = F.Id("j");
        Formula evidence = F.Id("y");
        Formula otherEvidence = F.Id("yPrime");
        Formula actionType = F.Id("A");
        Formula loss = Ell;
        Formula classMap = Call("quotientClass", law);
        Formula liftedLaw = Call("kerLift", law);
        Formula nnreal = Seq(
            Mathbb, Grp(F.Id("R")), Underscore, Grp(Geq, Sp, D(0)));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, lawType, Comma, Sp, parameter, Comma, Sp,
            evidenceType, Comma, Sp, Call("Finite", parameter), Comma, RowBreak, Grp(),
            law, Colon, Sp, state, Sp, To, Sp, lawType, Comma, Sp,
            joint, Colon, Sp, parameter, Sp, Times, Sp, evidenceType, Sp, To, Sp,
            nnreal, Comma, RowBreak, Grp(),
            OpenBracket,
            Call("Injective", liftedLaw), Sp, Land, Sp,
            law, Sp, Eq, Sp, liftedLaw, Sp, Circ, Sp, classMap,
            CloseBracket, Sp, Land, RowBreak, Grp(),
            OpenBracket, Forall, Sp, evidence, Comma, Sp, otherEvidence, Colon, Sp,
            evidenceType, Comma, Sp,
            Call("posterior", joint, evidence), Sp, Eq, Sp,
            Call("posterior", joint, otherEvidence), Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, actionType, Comma, Sp,
            loss, Colon, Sp, parameter, Sp, Times, Sp, actionType, Sp, To, Sp,
            real, Comma, RowBreak, Grp(),
            Call("conditionalBayesValue", joint, evidence, loss), Sp, Eq, Sp,
            Call("conditionalBayesValue", joint, otherEvidence, loss), Sp, Land,
            RowBreak, Grp(),
            Call("argmin", Call("conditionalRisk", joint, evidence, loss)), Sp, Eq, Sp,
            Call("argmin", Call("conditionalRisk", joint, otherEvidence, loss)),
            CloseBracket, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
