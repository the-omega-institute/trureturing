using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class EulerLayerInventoryGrowthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/EulerLayerInventoryGrowth.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same literal strict Euler inventory has a uniform square-root discrepancy from Chebyshev psi.",
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
                DescribeId.Create("positive-integer-log-factorization-split"),
                DeclarationHandle.Create(Prefix + "log_factorization_split"),
                H("First prime layer and truncated higher mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive natural U, log(U) is the sum of log(p) over "
                    + "its prime factors plus Q(U), the sum of Nat(factorization(p)-1)*log(p) "
                    + "over the same finite support. Each occupied valuation is at least "
                    + "one, so natural subtraction agrees there with subtraction after casting."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-divisibility-higher-layer-mass"),
                DeclarationHandle.Create(Prefix + "higher_layer_mass_mono"),
                H("Positive divisibility increases higher mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If positive natural A divides positive natural B, then Q(A)<=Q(B). "
                    + "Divisibility increases each valuation and includes the prime support "
                    + "of A in that of B. Natural truncated subtraction is monotone, log(p) "
                    + "is nonnegative, and the additional finite summands are nonnegative. "
                    + "A prime absent from A has Nat(0-1)=0; no negative first-layer term "
                    + "is introduced on extending the support."))),
                DescribeRole.Theorem),
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
                DescribeId.Create("literal-euler-inventory-higher-layer-bound"),
                DeclarationHandle.Create(Prefix + "strict_inventory_higher_layer_bound"),
                H("The full actual higher inventory has a finite square-root envelope"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real t>=2 and every positive natural U satisfying "
                        + "the same literal strict-count law, the complete sum of "
                        + "(U.factorization(q)-1)*log(q) over prime factors of U is at "
                        + "most 2*theta(sqrt(2*t))+2*(psi(t)-theta(t)). Natural "
                        + "subtraction in each valuation term is retained. The claim "
                        + "is for the actual strict integer; a forced least common "
                        + "multiple needs its own finite correction.")),
                    Paragraph(Text(
                        "An active exponent j satisfies q^j*log(q)<t*log(t), hence "
                        + "q^j<j*t. For an actual valuation a>=2, put k=floor(a/2). "
                        + "The actual layer 2*k is active and 2*k<=2^k<=q^k, so "
                        + "q^k<t. Therefore a-1<=2*Nat.log(q,floor(t)). The same "
                        + "prime also satisfies q^2<2*t from its actual second layer. "
                        + "Splitting Nat.log into Nat.log-1 and one charges the full "
                        + "same-prime mass to psi(t)-theta(t) and theta(sqrt(2*t)). "
                        + "No exponent is dropped and equality prices stay excluded."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("literal-euler-inventory-sqrt-discrepancy"),
                DeclarationHandle.Create(Prefix + "strict_inventory_sqrt_discrepancy"),
                H("A single square-root error bound for every real clock and strict integer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There is one real constant C>0 such that, for every real "
                        + "t>=2 and every positive natural U with the literal full "
                        + "strict prime-count law, |log(U)-psi(t)|<=C*sqrt(t). "
                        + "The constant is independent of both t and U, and weak "
                        + "psi includes its ordinary prime-power endpoints.")),
                    Paragraph(Text(
                        "Reuse the existing first-layer comparison with its full "
                        + "width-one boundary cost log(t), and the new complete "
                        + "higher-layer envelope. Mathlib supplies theta(y)<=log(4)*y "
                        + "and psi(t)-theta(t)<=c*sqrt(t). The elementary bounds "
                        + "log(t)<=2*sqrt(t) and sqrt(2*t)<=2*sqrt(t) yield one "
                        + "choice C=3+4*log(4)+abs(c). The proof assumes no RH, "
                        + "phase-density estimate, short-interval drift or signed "
                        + "zeta-zero control, and does not assert the sharper "
                        + "paper asymptotic with leading coefficient sqrt(2)-1."))),
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
                + "steps. These inventory estimates use no RH or Z7 premise "
                + "and do not prove Robin's inequality or the Riemann hypothesis.")))));
}
