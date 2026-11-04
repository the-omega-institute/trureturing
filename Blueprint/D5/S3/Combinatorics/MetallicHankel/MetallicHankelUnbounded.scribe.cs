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
            Node("metallic-hankel-normal-family", "The identical continuants at determinant-one boundaries", "normal_family", "For each n>=1, a single integral metallic series Phi exists and every integral series satisfying the same quadratic and constant coefficient condition equals Phi. The construction supplies the actual natural cycle of length L=3 when n=1 and L=6n-4 otherwise, with its golden or fractionData degrees, raw signs and denominator series. Its continuants start at Q_0=1 and Q_1=D_0 and follow Q_(p+2)=D_(p+1) Q_(p+1)-b_(p+1) q^(k_p+k_(p+1)+2) Q_p; Q_p has constant coefficient one and support at most s_p, with s_0=0 and s_(p+1)=s_p+k_p+1. For each K>=1, choose p=K L for even n and p=2K L for odd n. Then s_p=N=K rho, where rho=2n(n+1) for even n and rho=4n(n+1) for odd n. Define c_r=[q^(s_p-r)]Q_p only for r<=s_p, and d_r=[q^(s_(p-1)-r)]Q_(p-1) only for r<=s_(p-1); both are zero outside these ranges. The coefficient c_N and the coefficient d_(s_(p-1)) are one. The c moments against mu_i=[q^(n+1+i)]Phi vanish for every t<N, the length-N predecessor moments equal minus one at t=N-1 and zero at every earlier t, and det(mu_(a+b))_(a,b<N)=1. These assertions include n=1 and every K>=1. The same construction gives the bounded shift-n+1 row and the unbounded shift-n+3 row consumed by the unboundedness theorem. This contract supplies normal data for the full inverse theorem; it makes no assertion of arbitrary endpoint-jet polynomiality or higher-shift quasipolynomiality.", DescribeRole.Theorem),
            Node("metallic-hankel-unbounded-result", "Unboundedness at all shifts at least n+3", "result", "For every integer n at least one, there exists an integral formal power series Phi with constant coefficient one satisfying q Phi^2 + ((1+q^n)(1-q)-q[n]_q)Phi = 1, where [n]_q = 1+q+...+q^{n-1}. For every such Phi, every integer ell at least n+3 and every nonnegative integer M, some nonnegative integer j satisfies |Delta_j^{(ell)}| > M. Here Delta_j^{(ell)} is the determinant of the j by j matrix with entry [q^{ell+a+b}]Phi, with indices starting at zero and empty determinant one. At shift n+3 there is an explicit subsequence: for every positive integer k, Delta_{Pk-1}^{(n+3)} = (-1)^{nk} 2k lambda, where P = 4 and lambda = 1 when n = 1, and P = 2n(n+1) and lambda = 2n+1 when n is at least two. The cofactor identity and dual-number transfer give this linear growth. The row at shift n+1 is bounded in absolute value by one. Exponential coefficient growth and the bounded-strip theorem then exclude boundedness at every later shift. This establishes part 2 of Conjecture E of Han and Pedon for all positive n.", DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("han-pedon-metallic-hankel-unbounded"), ResolutionKind.Proved))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
