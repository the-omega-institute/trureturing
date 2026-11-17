using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class PrimeBoundarySecondOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/PrimeBoundarySecondOrder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second-order expansion of the original finite calibrated prime-prefix quantity.",
        H("Finite endpoints and normalization"),
        Blocks(
            Paragraph(Text("The finite-prefix Q is the original objective plus its tangent remainder. Original phi, baseline, realValues and realInfimum are imported without redefinition. This asymptotic does not assert integer Robin or RH.")),
            Describe.Lean(DescribeId.Create("primeboundarysecondorder-eventual-q-exact"),
                DeclarationHandle.Create(Prefix + "eventual_Q_exact"), H("The exact endpoint and tie identity for canonical Q"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Eventually C=1+H*ell=r^2 and the actual supported boundary is b(p)=max(1,log(C)/log(p)-1). Original prefixQ equals 2*(pi(r)*log r-theta(r))/(r^2-1)+pi(r)*[-log(1-r^-2)]+logarithmicTail(r,P). Consume the existing prime_prefix_boundary_formulas and fixed_price_Q_identity; r<P has already been proved from H/P->1. Tied primes p=r are counted in the inclusive head and have zero clock contribution. There is no assumption theta(P)<=P."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("primeboundarysecondorder-calibrated-q-second-order"),
                DeclarationHandle.Create(Prefix + "calibrated_Q_second_order"), H("Coefficients four, four, sixteen in the genuine r scale"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal conclusion is log(r)^2*(r*log(r)*prefixQ-4-4/log(r))->16. Equivalently Q=4/(r*l)*(1+1/l+4/l^2+o(l^-2)). The clock component contributes 2,4,12; the head contributes 1,1,2; and the tail contributes 1,-1,2 at the three successive powers. The four-term pi residual and theta_error_log_power 3 supply the errors at the moving r. C/(C-1) is retained and its log(r)^2 correction tends to zero. The first head/tail corrections cancel, leaving the requested second-order coefficient."))), DescribeRole.Theorem),
            Paragraph(Text("The finite square-prime tail expansion is supplied by the existing frozen PrimeSquareTail.prime_square_tail_logarithmic_refinements. Its second conjunct has the same strict (floor(y),floor(z)] prime sum and finite upper endpoint, with error 6/(y*log(y)^4)+5/(y*log(y)^9); the consumer keeps tailPolynomial as a private local abbreviation and converts this bound to 130/(y*log(y)^4) using log(y)>=1. The higher logarithmic Euler-power correction is controlled by QuantitativePrimeAbel.finite_logarithmic_tail_squeeze and the actual tail_euler_error and head_euler_error comparisons. No FinitePrimeTailSecondOrder package or public tail wrapper is part of this consumer closure.")),
            Paragraph(Text("The finite endpoint is paid explicitly: prove r*log(r)^3/P->0 by squaring and using C/(H*ell)->1, log r/ell->1/2, H/P->1 and ell^7/H->0. Then r*log(r)^3*T(P)->0. The quantitative prime-counting and theta remainders come from QuantitativePrimeAbel; the prefix scales come from RealInfimumPrimeBoundary.")),
            Paragraph(Text("The complete three-coefficient expansion retains the finite endpoint correction before passing to the prefix limit.")))));
}
