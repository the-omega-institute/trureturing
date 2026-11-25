using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.LeechFrame;

internal sealed class NormFourMixedProductsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The singular mixed products of signed norm-four states vanish for opposite signs or orthogonal directions.",
        H("Mixed Products of Norm-Four Lattice States"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normfourvirasorovector-opposite-sign-products"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LeechFrame/NormFourMixedProducts.opposite_sign_products"),
                H("Opposite signs in one norm-four direction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a norm-four charge and s² = 1, every nonnegative product "
                    + "of the states of signs s and −s vanishes. The mixed terms cancel, and the "
                    + "quadratic and charged terms cancel in degrees zero through three. Their "
                    + "higher products vanish by the self-product tail formulas."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normfourvirasorovector-orthogonal-products"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LeechFrame/NormFourMixedProducts.orthogonal_products"),
                H("Products of states in orthogonal directions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For orthogonal charges and arbitrary scalars, all nonnegative "
                    + "mixed products vanish. Orthogonality removes the current contractions, and "
                    + "negative creation-coefficient indices give the ground-product vanishing."))),
                DescribeRole.Theorem))));
}
