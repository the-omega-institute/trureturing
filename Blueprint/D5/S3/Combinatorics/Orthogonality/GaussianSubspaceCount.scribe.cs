using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;

internal sealed class GaussianSubspaceCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Orthogonality/GaussianSubspaceCount.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/nikandish2026orthogonality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Gaussian-binomial bridge for the complete binary submodule lattice.",
        H("Counting subspaces by their ordered frames"),
        Blocks(
            Describe.Lean(DescribeId.Create("gaussian-coefficient-two"),
                DeclarationHandle.Create(Prefix + "gaussian"), H("The product formula"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The coefficient [n choose d]_2 is the product of (2^n-2^i), "
                    + "for 0<=i<d, divided by the product of (2^d-2^i). This is "
                    + "defined arithmetically, independently of the subspace count."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dimension-subspace-card"),
                DeclarationHandle.Create(Prefix + "dimension_card"), H("Each dimension"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every 0<=d<=n, the number of actual d-dimensional "
                    + "Submodule (ZMod 2) (Fin n -> ZMod 2) objects equals this "
                    + "coefficient. An independent d-frame has a unique actual "
                    + "span. Conversely each such subspace contributes all of its "
                    + "ordered bases. The explicit sigma equivalence partitions "
                    + "the frames by their span; Mathlib's finite-frame formula "
                    + "counts the ambient frames and each basis fiber. The basis "
                    + "factor is positive, including the empty product at d=0."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-nonzero-lattice-sum"),
                DeclarationHandle.Create(Prefix + "result"), H("All nonzero subspaces"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every n, NikandishClique.nonzeroSubspaceCount n equals "
                    + "the sum of [n choose d]_2 over 1<=d<=n. A second explicit "
                    + "sigma equivalence partitions every nonzero submodule by "
                    + "its finrank; zero rank is equivalent to the zero submodule. "
                    + "Thus the empty n=0 sum is zero. Combined with the existing "
                    + "clique result this supplies its displayed Gaussian-binomial "
                    + "formula without re-proving the radical-quotient argument. "
                    + "The proofs are independently written from the standard "
                    + "frame-count argument and the source's full lattice domain."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Orthogonality/NikandishClique"))]));
}
