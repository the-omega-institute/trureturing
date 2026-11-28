using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class NormTwoTernarySyndromeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A short ternary syndrome criterion excludes squared norm two.",
        H("The Ternary Syndrome Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("norm-two-ternary-syndrome-injective"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/Orbifold/NormTwoTernarySyndrome.bilinear_ne_two_of_short_syndrome_injective"),
            H("Short-syndrome injectivity excludes squared norm two"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For an integral pairing matrix whose row Gram matrix is twelve times the lattice Gram matrix, assume "
                + "each row has constant parity across its columns and there are more than 24 columns. If the ternary "
                + "syndrome is injective on words of Hamming weight at most three, no lattice charge has squared norm two."))),
            DescribeRole.Theorem))));
}
