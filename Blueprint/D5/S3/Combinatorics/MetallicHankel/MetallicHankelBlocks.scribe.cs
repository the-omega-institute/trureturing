using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MetallicHankel;

internal sealed class MetallicHankelBlocksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/han2025hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordinary and reversed transfers act on the same continuants returned by normal_family.",
        H("Ordinary and Reversed Blocks of the Metallic Continuants"),
        Blocks(
            Node("metallic-hankel-blocks-prefix", "Ordered transfer products", "transferPrefix",
                "For a sequence A of two by two matrices over integral formal power series, define T(0)=I and T(p+1)=A(p)T(p). Thus later transitions multiply on the left.", DescribeRole.Definition),
            Node("metallic-hankel-blocks-step", "The cyclic ordinary transition", "ordinaryStep",
                "Given a natural L, degree indices k, integer signs b and denominator series D, A(p) has first row D(p), -b(p) X^(k(p+L-1)+k(p)+2) and second row 1,0. Natural subtraction is truncated at zero. At a positive period L the first exponent uses the last degree increment of the cycle.", DescribeRole.Definition),
            Node("metallic-hankel-blocks-ordinary", "Exact ordinary block action", "ordinary_blocks",
                "Let n>=1. Supply L,k,b,D,Q with exactly the explicit cycle data, length, initial values Q(0)=1, Q(1)=D(0), and recurrence exported by normal_family. Set nu=1 for even n and 2 for odd n; set rho=2n(n+1) for even n and 4n(n+1) for odd n. For U=T(L)^nu, constantCoeff(trace U)=1 and det U=X^(2rho). For every K>=1, put p=(K nu)L. Then U^K(1,0)=(Q(p),Q(p-1)). Moreover every degree sequence s satisfying s(p+1)=s(p)+k(p)+1 has s(p)=s(p-1)+(n+1) at all these block endpoints. The exceptional n=1 cycle has length three and weight four; its chosen block is doubled. The proof derives the actual state cycle, the sign product and weight, then multiplies the supplied recurrence. No assertion that trace U itself equals one is made. Taking s(p)=K rho from normal_family gives the predecessor degree K rho-(n+1). MetallicHankelEndpointJets consumes this exact ordinary block action to construct arbitrary endpoint jets.", DescribeRole.Theorem),
            Node("metallic-hankel-blocks-reverse-at", "Reversal at a supplied support degree", "reverseAt",
                "reverseAt(d,f) reflects the polynomial truncation through d. Its coefficient at r<=d is coeff(d-r,f), and every coefficient above d is zero. The support degree need not equal the actual degree; leading zero coefficients are retained.", DescribeRole.Definition),
            Node("metallic-hankel-blocks-reverse-coeff", "Coefficients of a specified-degree reversal", "reverse_coeff",
                "For every d,r and integral series f, coeff(r,reverseAt(d,f)) is coeff(d-r,f) when r<=d and zero otherwise. The endpoint-jet proof consumes this supported coefficient identity to identify both common-degree reversals, including the fixed predecessor shift.", DescribeRole.Theorem),
            Node("metallic-hankel-blocks-reversed-step", "The reversed continuant transition", "reversedStep",
                "For the same k,b,D, the reversed transition has first row reverseAt(k(p)+1,D(p)),-b(p) and second row 1,0. The off-diagonal entry has no power of X.", DescribeRole.Definition),
            Node("metallic-hankel-blocks-reversed", "Exact reversed block action", "reversed_blocks",
                "Let n>=1 and supply the very same L,k,b,D,Q data and recurrence as ordinary_blocks, together with s(0)=0, s(p+1)=s(p)+k(p)+1 and support(Q(p))<=s(p). These are the data exported by normal_family. Put nu=1 for even n and 2 for odd n, and R=T_reversed(L)^nu. Then R evaluated at X=0 is the identity matrix. For every K>=1, with p=(K nu)L, R^K(1,0) is (reverseAt(s(p),Q(p)),reverseAt(s(p-1),Q(p-1))). The proof reverses the actual supported recurrence and identifies the complete constant monodromy from both basis vectors. It includes the exceptional golden n=1 cycle. Combined with ordinary_blocks and s(p)=K rho, the predecessor support degree is K rho-(n+1). No arbitrary-order endpoint polynomial or full Conjecture C is asserted here.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
