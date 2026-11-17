using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.PartialTransposeSaturation;

internal sealed class PartialTransposeChainSplittingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/PartialTransposeSaturation/ChainSplitting.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/wangchen2025partialtranspose");

    private static DocumentBlock Desc(string name, string title, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shortest polynomial kernel chains split a pair of linear maps",
        H("Simultaneous chain projections"), Blocks(
            Paragraph(Text("Let f and g be linear maps from U to V over an arbitrary field. A coefficient chain u of length r plus one satisfies f(u0)=0, f(ui)=g(u(i-1)) at every interior position, and g(ur)=0. The construction chooses a shortest chain with nonzero final coefficient. It produces simultaneous complementary subspaces for both arrows without assuming a matrix pencil decomposition.")),
            Paragraph(Text("For a positive shortest degree, truncate the coefficient map one position earlier. The first image coefficient is outside its range: any preimage would subtract from the tail of the original chain and create a shorter chain with the same nonzero final coefficient. A linear functional separating that vector from the range gives a dual chain. Its pairings with the image chain are constant on diagonals and vanish off the main diagonal. Normalization makes the two chain families biorthogonal. The resulting finite sums of coordinate functionals are commuting projections.")),
            Desc("boundary", "Polynomial pencil coefficient map",
                "For a coefficient vector of length n, return the n plus one coefficients of (f-tg)u(t), including both endpoint equations. This definition applies also at n=0.", DescribeRole.Definition),
            Desc("boundary_injective_of_no_chain", "No kernel chains implies coefficient injectivity",
                "Suppose every finite coefficient chain with zero boundary has zero final coefficient. Every truncated coefficient map is injective. Remove the final zero coefficient repeatedly; the length zero coefficient space contains only zero."),
            Desc("split_common_kernel_line", "A common zero column splits off",
                "A nonzero vector killed by both arrows spans a direct summand of U. There is a projection P onto this line with f composed with P and g composed with P both zero. The line and the kernel of P are complementary, giving the degree zero singular summand."),
            Desc("split_shortest_chain", "A positive shortest chain is a simultaneous summand",
                "A shortest chain of length n plus two admits projections P on U and Q on V onto the coefficient-chain span and image-chain span. Both spans have the displayed independent chain bases. The equalities Qf=fP and Qg=gP hold on the entire domain, and each chain span is complementary to the corresponding projection kernel. The restrictions are the two shift arrows of a right singular block of index n plus one."),
            Desc("finrank_range_split", "A commuting projection splits image dimension",
                "For a linear map T into a finite-dimensional output space, let P and Q be linear endomorphisms with Q squared equal to Q and QT=TP. The dimension of the image of T is the sum of the dimensions of the images of QT and (identity-Q)T. These two images lie in the image of T, sum to it, and intersect trivially."),
            Desc("finrank_tensorSum_split", "A simultaneous pair splitting splits every tensor sum",
                "Suppose Q is idempotent and Qf1=f1P, Qf2=f2P. For any other pair g1,g2 with finite-dimensional output, the image dimension of f1 tensor g1 plus f2 tensor g2 is the sum of its components projected by Q tensor identity and its complementary projection. No coordinates on either summand are chosen."))));
}
