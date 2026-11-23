using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PetzPhysicalFirstVariationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary Petz on the physical two-flag path.",
        H("Ordinary Petz on the physical two-flag path"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("physical-firstvariation"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/PetzPhysicalFirstVariation.physical_firstVariation"),
                H("Joint recovery and retained-source derivatives"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The common reference scale cancels in each Petz block. Differentiating the product with the physical source path gives the two real flag coherences and zero derivative in the other entries."))),
                DescribeRole.Theorem))));
}
