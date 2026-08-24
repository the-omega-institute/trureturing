using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Interventions;

internal sealed class ObservationInterventionSeparationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Opposite Boolean causal directions can agree observationally while separating under intervention.",
        H("Observation-Intervention Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("observation-is-strictly-weaker-than-intervention"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Interventions/"
                        + "ObservationInterventionSeparation."
                        + "observation_strictly_weaker_than_intervention"),
                H("Observation is strictly weaker than intervention"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The two witness models have opposite causal directions but use the "
                            + "identity as both their root and child mechanisms. For every "
                            + "exogenous input, each model therefore produces the same observed "
                            + "pair, so their observational maps coincide.")),
                    Paragraph(Text(
                        "Fixing X to false separates the models when the exogenous input is true. "
                            + "The X-causes-Y model returns (false, false), whereas the Y-causes-X "
                            + "model returns (false, true). Their intervention maps are thus "
                            + "unequal despite observational equality."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula modelType = F.Id("DeterministicBoolSCM");
        Formula firstModel = F.Id("M");
        Formula secondModel = F.Id("N");
        Formula observationalEquality = Equal(
            Apply(F.Id("Obs"), firstModel),
            Apply(F.Id("Obs"), secondModel));
        Formula interventionInequality = NotEqual(
            Apply(F.Id("Int"), firstModel),
            Apply(F.Id("Int"), secondModel));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("M", modelType), Bound("N", modelType)],
            new Formula.Logic(
                observationalEquality,
                FormulaLogicOperator.And,
                interventionInequality)));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
