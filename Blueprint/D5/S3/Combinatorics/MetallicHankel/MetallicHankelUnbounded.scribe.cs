using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MetallicHankel;

internal sealed class MetallicHankelUnboundedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnbounded.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/han2025hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every n at least one, the shifted Hankel determinants of the q-metallic series are unbounded in absolute value at every shift at least n+3.",
        H("Han and Pedon's Metallic Hankel Conjecture, Part 2"),
        Blocks(
            Node("metallic-hankel-unbounded-result", "Unboundedness at all shifts at least n+3", "result", "For every integer n at least one, there exists an integral formal power series Phi with constant coefficient one satisfying q Phi^2 + ((1+q^n)(1-q)-q[n]_q)Phi = 1, where [n]_q = 1+q+...+q^{n-1}. For every such Phi, every integer ell at least n+3 and every nonnegative integer M, some nonnegative integer j satisfies |Delta_j^{(ell)}| > M. Here Delta_j^{(ell)} is the determinant of the j by j matrix with entry [q^{ell+a+b}]Phi, with indices starting at zero and empty determinant one. At shift n+3 there is an explicit subsequence: for every positive integer k, Delta_{Pk-1}^{(n+3)} = (-1)^{nk} 2k lambda, where P = 4 and lambda = 1 when n = 1, and P = 2n(n+1) and lambda = 2n+1 when n is at least two. The cofactor identity and dual-number transfer give this linear growth. The row at shift n+1 is bounded in absolute value by one. Exponential coefficient growth and the bounded-strip theorem then exclude boundedness at every later shift. This establishes part 2 of Conjecture E of Han and Pedon for all positive n.", DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("han-pedon-metallic-hankel-unbounded"), ResolutionKind.Proved))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
