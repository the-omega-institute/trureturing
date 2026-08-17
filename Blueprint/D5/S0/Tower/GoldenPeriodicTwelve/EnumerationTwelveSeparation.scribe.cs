using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.GoldenPeriodicTwelve;

internal sealed class EnumerationTwelveSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var representatives = Id("goldenPeriodicOrbitRepresentativesExactlyTwelve");
        var lowBound = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("O"),
            representatives,
            new Formula.Relation(
                Call(
                    "goldenStateArm",
                    Call("decodeGoldenState", Call("lowState", Id("O")))),
                FormulaRelationOperator.LessThanOrEqual,
                Id("goldenThreshold")));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The period-twelve phases admit a five-step partition and low-arm witnesses.",
            H("Period-Twelve Five-Step Separation"),
            Blocks(
                Paragraph(Text(
                    "Twenty-one legal five-step prefixes partition every inherited and new "
                        + "phase fixed by the twelfth iterate.")),
                Describe.Lean(
                    DescribeId.Create("period-twelve-low-arms-obey-the-golden-bound"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveSeparation."
                            + "golden_new_periodic_orbit_low_arms_bounded_twelve"),
                    H("Period-twelve low arms obey the golden bound"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(lowBound)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Each primitive twelve-cycle has an explicit phase whose arm is at "
                            + "most the exact golden threshold."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create(
                        "D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveDisjointB")),
            ]));
    }
}
