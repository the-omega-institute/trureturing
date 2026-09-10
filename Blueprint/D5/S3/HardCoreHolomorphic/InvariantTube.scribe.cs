using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HardCoreHolomorphic;

internal sealed class InvariantTubeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit holomorphic hard-core coordinates and uniform complex neighborhoods.",
        H("InvariantTube"),
        Blocks(
            Describe.Lean(DescribeId.Create("hc-holo-invarianttube-row-at-centers"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/InvariantTube.row_at_centers"),
                H("row at centers"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real centers are mapped to the correct real parent center, for every pruning set including the leaf and activity zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-holo-invarianttube-jacobian-tube-sum"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/InvariantTube.jacobian_tube_sum"),
                H("jacobian tube sum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual complex Jacobian retains a strict margin on the entire tube. The real-row value at the chosen real anchor suffices for this local comparison."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-holo-invarianttube-row-tube-stability"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/InvariantTube.row_tube_stability"),
                H("row tube stability"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Uniform stability is derived by integrating the true differential along straight message/activity segments. There is no supplied complex Lipschitz or complex-invariance premise."))), DescribeRole.Theorem))));
}
