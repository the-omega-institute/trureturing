using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class BarnesWallQ8CyclicGaugeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclic gauges for the quaternion anomaly detector",
        H("Cyclic gauges for the quaternion anomaly detector"),
        Blocks(Describe.Lean(
            DescribeId.Create("barnes-wall-q8-phase-detection"),
            DeclarationHandle.Create("D5/S3/HomologicalAlgebra/BarnesWallQ8CyclicGauge.zero_exponent_of_positive_trace_product"),
            H("The product of the three cyclic signs determines the inflated class"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/keller2026barneswall")),
            Blocks(Paragraph(Text(
                "The same binary carry cochain trivializes the restriction of the candidate to all " +
                "three order-four subgroups. Its tensorator changes each degree-two centralizer sign " +
                "by the candidate phase. The three positive cyclic traces and the positive global " +
                "trace product force that phase to be trivial."))),
            DescribeRole.Theorem))));
}
