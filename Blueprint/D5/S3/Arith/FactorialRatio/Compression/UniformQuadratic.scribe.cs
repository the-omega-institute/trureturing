using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio.Compression;

internal sealed class UniformQuadraticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/Compression/UniformQuadratic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The compact factorial gcd has a uniform quadratic logarithmic excess over the exact tail LCM.",
        H("Uniform quadratic compression loss"),
        Blocks(
            Paragraph(Text(
                "For natural r>=2 and 0<=s<r^2, let G be the gcd, over integers "
                + "0<=b<=floor(s/r), of the product over 0<=i<r of "
                + "((i+1)b)! (s-ib)! / b!. Put T=tailLCM(rs+r-1,r-1), where "
                + "tailLCM(H,M) is the product, over M<k<=H, of the least common "
                + "multiple of the positive integers at most floor(H/k). The exact "
                + "divisibility T|G makes E=G/T a positive integer.")),
            Describe.Lean(
                DescribeId.Create("uniform-quadratic-log-bound"),
                DeclarationHandle.Create(Prefix + "uniform_quadratic_log_bound"),
                H("An unconditional bound with an explicit constant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural r,s with r>=2 and s<r^2, "
                        + "0<=log(compactExcess(r,s))<=(12+19 log 4)r^2. "
                        + "All logarithms are natural. Since log 4=2 log 2, the "
                        + "constant is 12+38 log 2. There is no asymptotic "
                        + "threshold and no unproved analytic hypothesis.")),
                    Paragraph(Text(
                        "For p<=r, the parameter b=0 bounds the exponent of p "
                        + "in E by (r-1)floor(log_p(s)). Because s<r^2 and p<=r, "
                        + "floor(log_p(s))<=3 floor(log_p(r)). Summing against "
                        + "log p gives a small-prime contribution at most "
                        + "3(r-1)psi(r). The elementary bound "
                        + "psi(r)<=(log 4+4)r therefore makes this contribution "
                        + "at most 3(log 4+4)r^2.")),
                    Paragraph(Text(
                        "For r<p<=s, put a=r/sqrt(p), A=floor(a), and "
                        + "K=floor(s/p). Both A and K are at least one. If A<=K, "
                        + "choose k=A; the inequalities k<=a<=2k turn the local "
                        + "bound 2k+2r^2/(kp) into 6r/sqrt(p). If K<A, choose "
                        + "k=K; then k<=a and s<=2kp give the bound "
                        + "2r/sqrt(p)+4r^2/s. Thus every large prime has "
                        + "exponent at most 6r/sqrt(p)+4r^2/s. These choices "
                        + "always satisfy 1<=k and kp<=s, so their compact "
                        + "parameters b=floor(kp/r) are legal.")),
                    Paragraph(Text(
                        "A finite summation-by-parts estimate says that "
                        + "a sequence with w(0)=0 and partial sums "
                        + "sum_{i<=n}w(i)<=An satisfies "
                        + "sum_{i<=N}w(i)/sqrt(i)<=2A sqrt(N). The strengthened "
                        + "induction bound is A sqrt(N) plus the partial sum "
                        + "divided by sqrt(N); its step uses "
                        + "n(1/sqrt(n)-1/sqrt(n+1))<=sqrt(n+1)-sqrt(n). "
                        + "Applying this to w(p)=log p on primes and zero "
                        + "otherwise, with theta(n)<=(log 4)n, bounds the "
                        + "large-prime logarithmic contribution by "
                        + "12(log 4)r sqrt(s)+4(log 4)r^2<=16(log 4)r^2. "
                        + "Primes above s have zero exponent. Adding the two "
                        + "ranges gives the stated constant.")),
                    Paragraph(Text(
                        "The argument includes s=0 and s<r, when b=0 is the "
                        + "only parameter. At r=M+1 and s=M(M-1), M>=1, it "
                        + "also gives log(E)/M<=4(12+19 log 4)M. With x=M^2 "
                        + "this is an explicit O(sqrt(x)) normalized loss; "
                        + "at M=n^2 it is O(n^2) on the quartic scale x=n^4. "
                        + "This consequence bounds the loss of the gcd of the "
                        + "whole compact family."))),
                DescribeRole.Theorem))));
}
