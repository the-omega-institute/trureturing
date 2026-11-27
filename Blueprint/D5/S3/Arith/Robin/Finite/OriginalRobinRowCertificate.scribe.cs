using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Finite;

internal sealed class OriginalRobinRowCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rational checker proves the original Robin inequality on each certified interval.",
        H("A rational checker for Robin intervals"),
        Blocks(
            Paragraph(Text(
                "The checker proves optimality from the layer cuts and bounds the objective "
                + "and endpoint margins with exact rational logarithm estimates. Concavity "
                + "gives the margin throughout the interval.")),
            Describe.Lean(
                DescribeId.Create("robin-original-rows-05"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Finite/OriginalRobinRowCertificate.original_robin_through_pinned_row05"),
                H("Robin inequality through Row 05"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The checked Row 05 data extend the original inequality to every natural n greater than 5040 with log n at most 223.373126."))),
                DescribeRole.Theorem))));
}
