using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.GoldenPeriodic;

internal sealed class EnumerationElevenSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var representatives = Id("goldenPeriodicOrbitRepresentativesExactlyEleven");
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
            "The period-eleven phases admit bounded prefix partitions and low-arm witnesses.",
            H("Period-Eleven Prefix Separation"),
            Blocks(
                Paragraph(Text(
                    "Three-step prefixes partition every expected phase; the three 34-state "
                        + "blocks are refined once more by their fourth step.")),
                Describe.Lean(
                    DescribeId.Create("period-eleven-low-arms-obey-the-golden-bound"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationElevenSeparation."
                            + "golden_new_periodic_orbit_low_arms_bounded_eleven"),
                    H("Period-eleven low arms obey the golden bound"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(lowBound)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Each primitive eleven-cycle has an explicit phase whose arm is at "
                            + "most the exact golden threshold."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenPeriodic/EnumerationElevenDisjoint")),
            ]));
    }
}
