using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold.Paley;

internal sealed class P48pSyndromeFrameDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pSyndromeFrame.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The concrete P48p frame reduces norm-two exclusion to a ternary syndrome check.",
        H("The P48p Pairing Frame"),
        Blocks(
            Describe.Lean(DescribeId.Create("p48p-frame-orthogonality"),
                DeclarationHandle.Create(Prefix + "p48pFrameRows_orthogonal"),
                H("The catalogue frame has norm twelve"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integral row computations prove that the frame Gram matrix "
                    + "is twelve times the identity in the Nebe–Sloane P48p catalogue basis."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("p48p-rootlessness-from-syndromes"),
                DeclarationHandle.Create(Prefix + "p48p_catalogue_rootless"),
                H("Norm-two exclusion from the short syndromes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact pairing identity and column congruences permit the "
                    + "ternary syndrome criterion on the actual catalogue lattice. The remaining "
                    + "premise is injectivity on words of weight at most three."))),
                DescribeRole.Theorem))));
}
