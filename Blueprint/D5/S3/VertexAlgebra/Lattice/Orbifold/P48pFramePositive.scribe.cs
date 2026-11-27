using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class P48pFramePositiveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The checked norm-twelve frame proves positive definiteness of the P48p catalogue Gram matrix.",
        H("Positive Definiteness of the P48p Gram Matrix"),
        Blocks(
            Describe.Lean(DescribeId.Create("p48p-gram-posdef"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/Orbifold/P48pFramePositive.p48pGram_posDef"),
                H("The catalogue Gram matrix is positive definite"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over the reals, let G be the Nebe–Sloane P48p catalogue Gram matrix and U "
                    + "the rows of the existing orthogonal norm-twelve frame. The checked pairing matrix F = GUᵀ "
                    + "satisfies UF = 12I, so F is invertible. The same certificate gives FFᵀ = 12G. "
                    + "Thus G = (1/12)FFᵀ is positive definite, using only the existing frame."))),
                DescribeRole.Theorem))));
}
