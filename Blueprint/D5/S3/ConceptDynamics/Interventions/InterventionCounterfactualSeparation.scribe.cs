using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Interventions;

internal sealed class InterventionCounterfactualSeparationDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Interventions/InterventionCounterfactualSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two Boolean causal models can agree on every interventional marginal while "
            + "disagreeing on a unit-level counterfactual.",
        H("Intervention-Counterfactual Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("interventional-marginals-do-not-determine-counterfactuals"),
                DeclarationHandle.Create(DeclarationPrefix +
                    "intervention_strictly_weaker_than_counterfactual"),
                H("Interventional marginals do not determine counterfactuals"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A deterministic Boolean causal model assigns an outcome to each "
                            + "exogenous unit and imposed treatment. Its interventional marginal "
                            + "counts outcomes over the uniform two-unit exogenous population, "
                            + "whereas its counterfactual retains the unit while replacing the "
                            + "treatment.")),
                    Paragraph(Text(
                        "The first witness ignores treatment and returns the exogenous bit. The "
                            + "second preserves that bit under false treatment and complements it "
                            + "under true treatment. For either treatment, each model produces "
                            + "one false outcome and one true outcome, so all interventional "
                            + "counts agree.")),
                    Paragraph(Text(
                        "For the false exogenous unit with true as the alternate treatment, the "
                            + "first model returns false and the second returns true. Their "
                            + "unit-level counterfactual functions therefore differ despite "
                            + "identical interventional marginals."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula modelType = F.Id("DeterministicBoolSCM");
        Formula firstModel = F.Id("M");
        Formula secondModel = F.Id("N");
        Formula sameInterventions = Equal(
            Call("Int", firstModel),
            Call("Int", secondModel));
        Formula differentCounterfactuals = NotEqual(
            Call("CF", firstModel),
            Call("CF", secondModel));

        return Disp(Seq(
            Exists, Sp, firstModel, Comma, Sp, secondModel, Colon, Sp, modelType, Comma, Sp,
            sameInterventions, Sp, Land, Sp, differentCounterfactuals, Dot));
    }
}
