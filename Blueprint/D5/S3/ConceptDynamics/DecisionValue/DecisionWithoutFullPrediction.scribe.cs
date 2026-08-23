using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValue;

internal sealed class DecisionWithoutFullPredictionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One constant concept determines every optimal action without determining full payoffs.",
        H("Decision Sufficiency Without Full Prediction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("decision-sufficiency-without-full-prediction"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DecisionValue/DecisionWithoutFullPrediction."
                        + "decision_sufficiency_without_full_prediction"),
                H("Decision sufficiency does not require full prediction"),
                StatementSource.FromAuthor(SeparationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source has two states and two actions. Action a pays 10 and 100 "
                            + "at the respective states, while action b pays 0 and 1.")),
                    Paragraph(Text(
                        "The optimal-action concept is constructed as the set of actions whose "
                            + "payoff dominates every alternative. The full-result target records "
                            + "the complete action-payoff profile, and the concept readout is constant.")),
                    Paragraph(Text(
                        "Both optimal-action sets equal {a}, so the first target factors through "
                            + "the constant concept. The two full profiles differ at action a, so "
                            + "the second target cannot factor through that same concept."))),
                DescribeRole.Theorem))));

    private static Formula Refines(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula SeparationFormula()
    {
        Formula optimal = F.Id("optimalActions");
        Formula complete = F.Id("fullPayoffProfile");
        Formula constant = F.Id("constantConcept");

        return Disp(Seq(
            Refines(optimal, constant), Sp, Land, Sp,
            Neg, Sp, Refines(complete, constant), Dot));
    }
}
