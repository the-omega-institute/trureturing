using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicEight;

internal sealed class EnumerationEightMaximinADocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var lowArm = Id("tribonacciPeriodEightOrbitALowArm");
        var champion = Call("championValue", Id("t"));
        var bound = new Formula.Relation(
            lowArm,
            FormulaRelationOperator.LessThanOrEqual,
            champion);

        return DocumentDefinition.Create(ScribeNode.Create(
            "All fifteen primitive period-eight orbits have low arms below the champion.",
            H("Tribonacci Period-Eight Maximin Bounds"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("period-eight-orbit-a-low-arm-bound"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightMaximinA."
                            + "tribonacci_period_eight_orbit_a_low_arm"),
                    H("Period-eight orbit A has a bounded low arm"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(bound)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Fifteen separate exact cubic comparisons keep every maximin witness "
                            + "within the default tactic budget."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightFixed")),
            ]));
    }
}
