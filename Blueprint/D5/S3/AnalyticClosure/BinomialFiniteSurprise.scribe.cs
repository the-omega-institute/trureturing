using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class BinomialFiniteSurpriseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite binomial surprise has uniform Gaussian envelopes, partition bounds and moments.",
        H("Finite Binomial Surprise"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-binomial-surprise-all-natural-moments"),
            DeclarationHandle.Create(
                "D5/S3/AnalyticClosure/BinomialFiniteSurprise.result"),
            H("Actual finite masses and all natural surprise moments"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/ouimet2020precise")),
            Blocks(
                Paragraph(Text(
                    "Choose the constants before the binomial size, success parameter and escort "
                    + "parameter: U = 4 exp(1/8)/(1-exp(-1/8)), D = exp(-768)/2, "
                    + "c = min(3/128,D), C = 32+U, and K(k) = (U/D)(2(k+1))^k. "
                    + "The constants c and C and every K(k) are strictly positive.")),
                Paragraph(Text(
                    "For every natural N and every real p in [1/4,3/4], the support is "
                    + "the N+1 integers from zero through N. Its actual mass is "
                    + "q(n) = choose(N,n) p^n (1-p)^(N-n), using binomialMass. "
                    + "M is the maximum over this entire finite support, S(n) = -log(q(n)/M), "
                    + "Z(beta) = sum_n exp(-beta S(n)), and "
                    + "E(beta,k) = sum_n S(n)^k exp(-beta S(n))/Z(beta). "
                    + "Define w(beta,n) = exp(-beta S(n))/Z(beta), "
                    + "mu(beta) = sum_n w(beta,n) S(n), "
                    + "V(beta) = sum_n w(beta,n)(S(n)-mu(beta))^2, and "
                    + "H(beta) = sum_n w(beta,n)|S(n)-mu(beta)|^4. "
                    + "All sums use the actual finite support, and natural zero powers equal one.")),
                Paragraph(Text(
                    "The masses sum to one. At every support point q(n) is strictly positive, "
                    + "q(n) <= M and S(n) >= 0; also 0 < M <= 1. For every real beta, "
                    + "Z(beta) > 0, E(beta,0) = 1, all w(beta,n) are nonnegative and their sum is one.")),
                Paragraph(Text(
                    "If N >= 1, set m = floor((N+1)p), delta = (N+1)p-m, and "
                    + "z(n) = (n-Np)/sqrt(Np(1-p)). Then m <= N, M = binomialMass(p,N,m), "
                    + "and |m-Np| <= 1. If delta = 0, then m >= 1 and "
                    + "binomialMass(p,N,m-1) = M. For every support point put t = |n-m|. "
                    + "The simultaneous estimates are t(t-1)/(2N) <= S(n), "
                    + "(3/128)z(n)^2-1/2 <= S(n) <= 32(1+z(n)^2), and "
                    + "c z(n)^2-C <= S(n) <= C(1+z(n)^2).")),
                Paragraph(Text(
                    "For every N and p above, Z(1/2) <= U sqrt(N+1). For every real beta >= 1/2, "
                    + "Z(beta) <= Z(1/2). For every real alpha in [1,2], "
                    + "D sqrt(N+1) <= Z(alpha) <= U sqrt(N+1), "
                    + "c sqrt(N+1) <= Z(alpha) <= C sqrt(N+1), and for every natural k, "
                    + "0 <= E(alpha,k) <= K(k). The variance satisfies "
                    + "0 <= V(alpha) <= E(alpha,2) <= K(2). The centered fourth moment satisfies "
                    + "0 <= H(alpha) <= 16 E(alpha,4) <= 16 K(4).")),
                Paragraph(Text(
                    "If N = 0, every support index is zero, q(n) = 1, S(n) = 0 and M = 1. "
                    + "For every real beta, Z(beta) = 1 and E(beta,k) = 0 for every natural k >= 1. "
                    + "The bounds include both support endpoints, p = 1/4 and 3/4, "
                    + "alpha = 1 and 2, and tied modes.")),
                Paragraph(Text(
                    "The adjacent recurrence (i+1)(1-p)q(i+1) = (N-i)p q(i) establishes the floor mode. "
                    + "On each side of that mode, logarithmic increments telescope along the finite "
                    + "support. Their numerator-minus-denominator lies between s-1 and s. "
                    + "The lower scalar logarithm bound gives the t(t-1)/(2N) estimate. "
                    + "A crude global estimate S(n) <= 2N and the central denominators >= N/32 "
                    + "give the upper envelope, including the endpoints.")),
                Paragraph(Text(
                    "For N >= 1 choose L = ceil(sqrt(N)). A shell indexed by "
                    + "r = floor(|n-m|/L) has at most 2L points: its side and distance remainder "
                    + "identify each index. The surprise lower bound and the finite geometric sum "
                    + "with ratio exp(-1/8) give the half-temperature upper partition bound. "
                    + "For the lower bound choose ell = floor(sqrt(N+1)) and "
                    + "a = min(m,N+1-ell). The ell indices from a through a+ell-1 stay inside "
                    + "the support and contain m. On this clipped interval z(n)^2 <= 32/3 and "
                    + "S(n) <= 384, so every escort weight before normalization is at least exp(-768). "
                    + "Since ell >= sqrt(N+1)/2, this yields the stated lower partition bound.")),
                Paragraph(Text(
                    "For x >= 0 and every natural k, x^k exp(-x/2) <= (2(k+1))^k. "
                    + "For k >= 1 this follows by setting y = x/(2k) and using y exp(-y) <= 1; "
                    + "the zero power is treated directly. For alpha >= 1, the remaining exponential "
                    + "factor is bounded by exp(-x/2). Summing with x = S(n) and dividing by the "
                    + "positive lower partition bound proves every natural moment bound. "
                    + "Normalized finite weighted algebra gives V = E(alpha,2)-mu(alpha)^2. "
                    + "The even fourth-power inequality and finite weighted Jensen give "
                    + "H <= 8(E(alpha,4)+mu(alpha)^4) <= 16 E(alpha,4).")),
                Paragraph(Text(
                    "These are single-group estimates. A fourth-moment expansion for several low "
                    + "groups additionally requires an actual independent product law. Whether "
                    + "conditioning on an output preserves that law is a separate condition on the "
                    + "joint model. The local-limit literature supplies classical context; the "
                    + "finite uniform estimates here follow directly from adjacent mass ratios."))),
            DescribeRole.Theorem))));
}
