using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class OriginalMaximumPurePacketsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/OriginalMaximumPurePackets.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full original integer maximality is equivalent to all legal pure packet comparisons.",
        H("Original Maximum: Complete Pure Packets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("original-legal-integer-clock"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/OriginalMaximumPurePackets.legal_clock"),
                H("Every legal integer has clock greater than one"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive natural p and n>=1 with 5040*p dividing n, 1<log(n). The complete mandatory floor alone proves this statement. OriginalPrimeSourceOrder uses it at the legal opposite-class exchange competitors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-strict-loglog-rectangle"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/OriginalMaximumPurePackets.strict_loglog_rectangle"),
                H("Strict log-log curvature on a balanced rectangle"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real a,b,c,d with 1<a, a<b, a<c and a+d=b+c, log(log(a))+log(log(d))<log(log(b))+log(log(c)). The balance also places d in the positive-log domain. The legal two-prime exchange in OriginalPrimeSourceOrder consumes this existing strict rectangle."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The finite Euler min/max identity is AVB10 in the repository's "
                + "Library/ArithSums/nicolas2025comparison.md. The pure-packet "
                + "reduction follows LR7-LR15 of legal-replacement-main-upper-proof.md, "
                + "using exact Euler modularity and strict logarithmic curvature.")),
            Describe.Lean(
                DescribeId.Create("original-maximum-complete-pure-packets"),
                DeclarationHandle.Create(Prefix + "original_maximizes_iff_pure_packets"),
                H("All pure packets suffice for literal full-domain maximality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix natural numbers p,N with p positive, N at least "
                        + "one, and 5040*p dividing N. The result includes "
                        + "every prime forcing label and in fact needs only "
                        + "its positivity. Then OriginalFirstClockTransport."
                        + "originalMaximizes(p,N) holds if and only if both "
                        + "of the following complete families hold: every "
                        + "positive D divisible by 5040*p and dividing N has "
                        + "originalObjective(D)<=originalObjective(N); and "
                        + "every positive U divisible by 5040*p and divisible "
                        + "by N has originalObjective(U)<=originalObjective(N). "
                        + "The objective remains exactly log(sigma(n)/n) "
                        + "minus log(log(log(n))), with actual sigma(1,n) "
                        + "and natural integer arguments.")),
                    Paragraph(Text(
                        "A packet can change any finite collection of prime "
                        + "bases and any number of layers in each stack. "
                        + "There is no one-prime, one-layer, squarefree or "
                        + "clock-ceiling restriction. These hypotheses are "
                        + "all pure integer comparisons, not the necessary "
                        + "one-layer derivative or inventory conditions.")),
                    Paragraph(Text(
                        "For any positive legal competitor M, put G=gcd(N,M) "
                        + "and H=lcm(N,M). Both are positive and divisible "
                        + "by the complete mandatory floor 5040*p. In "
                        + "particular the gcd keeps every mandatory layer, "
                        + "including the forcing prime even when it already "
                        + "divides 5040. No exponent-one premise on p is "
                        + "used. G divides N and N divides H, so the proposed "
                        + "pure families compare both actual integers.")),
                    Paragraph(Text(
                        "Write W(n)=log(sigma(n)/n). At price zero, the "
                        + "existing golden_resource_sigma_identity and "
                        + "golden_resource_objective_sum_on express each "
                        + "W as its exact sum of prime-local objectives. "
                        + "Use one finite support containing the prime "
                        + "factors of G,H,N,M. At each prime the exponents "
                        + "of G,H are the minimum and maximum of the "
                        + "exponents of N,M, hence the same unordered pair. "
                        + "Summing proves W(G)+W(H)=W(N)+W(M). This "
                        + "auxiliary exact identity does not replace the "
                        + "nonlinear objective being compared.")),
                    Paragraph(Text(
                        "The natural identity G*H=N*M gives a+d=b+c "
                        + "for a=log(G), b=log(N), c=log(M), d=log(H). "
                        + "The floor gives a>1, so every logarithm below "
                        + "lies in its actual positive domain. If M is "
                        + "incomparable with N in divisibility, then a<b "
                        + "and a<c. First (b-a)*(c-a)>0 yields a*d<b*c, "
                        + "and taking logarithms gives log(a)+log(d) "
                        + "<log(b)+log(c). Multiplying by log(a)>0 "
                        + "and adding (log(b)-log(a))*(log(c)-log(a))>=0 "
                        + "gives log(a)*log(d)<log(b)*log(c). Taking "
                        + "logarithms again proves f(a)+f(d)<f(b)+f(c), "
                        + "where f(x)=log(log(x)). Thus the exact rectangle "
                        + "Xi=f(b)+f(c)-f(a)-f(d) is strictly positive.")),
                    Paragraph(Text(
                        "Euler modularity gives the exact deficit identity "
                        + "F(N)-F(M)=[F(N)-F(G)]+[F(N)-F(H)]+Xi, "
                        + "where F is the original objective. The two pure "
                        + "deficits are nonnegative, so an incomparable "
                        + "M is strictly worse. Comparable competitors "
                        + "are already members of one pure family; their "
                        + "rectangle is zero. This proves the converse. "
                        + "The forward implication restricts the literal "
                        + "full-domain comparison to its two pure families. "
                        + "No source existence, maximizing selector, "
                        + "inventory or mixed-loss field is assumed.")),
                    Paragraph(Text(
                        "Consequently every original maximizing tie "
                        + "strictly beats every legal integer incomparable "
                        + "with it. Any two maximizing ties in this same "
                        + "forced domain must therefore be comparable "
                        + "in divisibility. The strict mixed step applies "
                        + "uniformly to all maximizing ties; no attainment "
                        + "is assumed.")),
                    Paragraph(Text(
                        "This finite reduction does not establish the "
                        + "pure comparison families themselves, cofinal "
                        + "original sources, or a uniform JC18 initial "
                        + "arithmetic-height payment. It supplies no MAIN "
                        + "upper bound, applicable full R0/R_eta "
                        + "contradiction, strict Robin inequality for "
                        + "every n>5040, or RH. All original chain, "
                        + "activation and terminal trace obligations "
                        + "of those later arguments remain in place."))),
                DescribeRole.Theorem))));
}
