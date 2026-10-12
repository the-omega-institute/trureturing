using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class EulerLayerInventoryGrowthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/EulerLayerInventoryGrowth.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The logarithm of the same literal strict Euler inventory grows uniformly like its clock.",
        H("Literal Strict Euler Inventory Growth"),
        Blocks(
            Paragraph(Text(
                "For a real t>1, set lambda(t)=1/(t*log(t)). A positive natural integer U "
                + "has the strict inventory law when, for every natural prime q, "
                + "U.factorization(q)=optimalLayerCount(lambda(t),q). The count includes "
                + "every positive natural exponent k for which lambda(t) is strictly less "
                + "than goldenLayerMarginal(q,k). Equal prices are excluded. The integer "
                + "U=1 and empty exponent prefixes remain in the domain. The simultaneous "
                + "positive integer specification supplies this law for every t>1.")),
            Describe.Lean(
                DescribeId.Create("literal-euler-inventory-chebyshev-bounds"),
                DeclarationHandle.Create(Prefix + "strict_inventory_chebyshev_bounds"),
                H("The finite first-prime and higher-valuation comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real t>=2 and every positive natural U satisfying "
                        + "the strict inventory law, put Y=t*log(t)/log(2). Then "
                        + "theta(t)-log(t)<=log(U) and "
                        + "log(U)<=theta(t)+psi(Y)-theta(Y). Here theta is the sum "
                        + "of log(q) over primes q<=t, and psi is the actual von Mangoldt "
                        + "sum over positive integers up to its argument.")),
                    Paragraph(Text(
                        "The first Euler marginal equals log(1+1/q)/log(q). Its upper "
                        + "bound excludes q>=t from the support of U, while its lower "
                        + "endpoint bound includes every prime with q+1<=t. Missing "
                        + "primes therefore lie in (t-1,t], which contains at most one "
                        + "natural integer, floor(t). Their total literal weight is "
                        + "at most log(t). No positivity of any individual prefix "
                        + "is imposed.")),
                    Paragraph(Text(
                        "For every active positive exponent k, the existing geometric "
                        + "marginal bound gives q^k*log(q)<t*log(t), hence q^k<Y. "
                        + "For each prime dividing U, its full valuation a consequently "
                        + "satisfies a<=Nat.log(q,floor(Y)). The sum of (a-1)*log(q) "
                        + "is bounded by the sum of (Nat.log(q,floor(Y))-1)*log(q) "
                        + "over all primes up to floor(Y). The exact Chebyshev "
                        + "prime-log identities identify the latter with psi(Y)-theta(Y). "
                        + "Finally log(U) is the first-prime sum plus this full excess. "
                        + "Actual activation clocks are never identified with q^k."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("literal-euler-inventory-uniform-growth"),
                DeclarationHandle.Create(Prefix + "strict_inventory_uniform_growth"),
                H("A common asymptotic threshold for every actual integer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real epsilon>0 there is a real T>1 such that, "
                        + "for every real t>=T and every positive natural U with "
                        + "the exact prime strict-count law, |log(U)/t-1|<epsilon. "
                        + "The threshold depends on epsilon and not on U.")),
                    Paragraph(Text(
                        "The unconditional MediumPNT gives psi(t)-t=O(t*exp("
                        + "-c*log(t)^(1/10))) for some c>0. The exponential tends to "
                        + "zero. Mathlib's existing estimate psi-theta=O(sqrt(t)) "
                        + "then gives theta(t)/t tending to one. Its global bound "
                        + "psi(Y)-theta(Y)<=C*sqrt(Y) controls the higher excess. "
                        + "Both log(t)/t and sqrt(t*log(t)/log(2))/t tend to zero; "
                        + "the square of the latter is log(t)/(t*log(2)). Dividing "
                        + "the finite bounds by t proves the uniform conclusion."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For a nonlinear winner in the original 5040*p source family with the same U, "
                + "t=log(U)+s "
                + "and s>0, identification of U with this strict inventory would "
                + "allow epsilon=1/2 to give log(U)>=t/2 eventually. The identity "
                + "itself gives log(U)<t. This is the scale transfer used by the "
                + "original all-label polynomial localization. The strict-core "
                + "identification, the fixed signed EL.9 estimate and the conditional "
                + "analytic localization remain separate hypotheses or unproved "
                + "steps. These two inventory theorems use no RH or Z7 premise "
                + "and do not prove Robin's inequality or the Riemann hypothesis.")))));
}
