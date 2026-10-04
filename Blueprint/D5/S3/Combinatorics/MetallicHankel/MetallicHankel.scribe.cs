using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MetallicHankel;

internal sealed class MetallicHankelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MetallicHankel/MetallicHankel.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/han2025hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every n at least two, the shift n+2 Hankel determinants of the q-metallic series have signed period 2n(n+1) and values in {-2,-1,0,1,2}.",
        H("Han and Pedon's Metallic Hankel Conjecture, Part 1"),
        Blocks(
            Node("metallic-hankel-result", "Periodicity and values at shift n+2", "result", "For every integer n at least two, there exists an integral formal power series Phi with constant coefficient one satisfying q Phi^2 + ((1+q^n)(1-q)-q[n]_q)Phi = 1, where [n]_q = 1+q+...+q^{n-1}. For every such Phi and every nonnegative integer j, define Delta_j^{(ell)} as the determinant of the j by j matrix with entry [q^{ell+a+b}]Phi, using indices starting at zero and empty determinant one. Then Delta_{j+2n(n+1)}^{(n+2)} = (-1)^n Delta_j^{(n+2)}, and Delta_j^{(n+2)} belongs to {-2,-1,0,1,2}. Thus the determinants are periodic when n is even and antiperiodic when n is odd. Integral quadratic tails produce monic moment relations; a two-coordinate transfer bounds their constant terms and a full cycle contributes the sign (-1)^n. The determinant relations extend the conclusion across all zero intervals. These identities establish part 1 of Conjecture E of Han and Pedon; they make no assertion about unboundedness at shifts at least n+3.", DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("han-pedon-metallic-hankel-shift"), ResolutionKind.Proved))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
