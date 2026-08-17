using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodic;

internal sealed class EnumerationSevenMaximinADocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var lowArm = Id("tribonacciPeriodSevenOrbitALowArm");
        var champion = Call("championValue", Id("t"));
        var bound = new Formula.Relation(
            lowArm,
            FormulaRelationOperator.LessThanOrEqual,
            champion);

        return DocumentDefinition.Create(ScribeNode.Create(
            "All ten period-seven orbits have low arms below the champion.",
            H("Tribonacci Period-Seven Maximin Bounds"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("period-seven-orbit-a-low-arm-bound"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodic/EnumerationSevenMaximinA."
                            + "tribonacci_period_seven_orbit_a_low_arm"),
                    H("Period-seven orbit A has a bounded low arm"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(bound)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Ten separate exact cubic comparisons keep each maximin witness "
                            + "within the default tactic budget."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodic/EnumerationSevenFixed")),
            ]));
    }
}
