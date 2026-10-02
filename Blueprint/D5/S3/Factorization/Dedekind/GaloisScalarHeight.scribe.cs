using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Dedekind;

internal sealed class GaloisScalarHeightDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolute scalar height under a field automorphism.",
        H("Absolute scalar height under a field automorphism"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("galois-scalar-height"),
                DeclarationHandle.Create("D5/S3/Factorization/Dedekind/GaloisScalarHeight.scalar_mul_height_galois"),
                H("Absolute scalar height under a field automorphism"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every number field K, every rational field automorphism sigma of K and every x in K, the absolute multiplicative scalar height of sigma(x) equals that of x.")),
                    Paragraph(Text("For an integral coordinate pair, the induced automorphism of the ring of integers preserves the absolute norm of its generated ideal. The same automorphism permutes infinite places while preserving real and complex multiplicities. These two calculations preserve the homogeneous pair height; an integral fraction representation supplies every scalar."))),
                DescribeRole.Theorem))));
}
