using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class OriginalHalfBinomialIntegralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized central-binomial series give the elliptic sine integral and the closed-interval arcsine expansion.",
        H("Original Half-Binomial Integrals and the Arcsine Expansion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("original-half-binomial-normalized-coefficient"),
                DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialIntegral.b"),
                H("The normalized central-binomial coefficient"),
                StatementSource.FromAuthor(Disp(Seq(Call("b", F.Id("n")), Eq,
                    Frac, Grp(Call("centralBinom", F.Id("n"))),
                    Grp(D(4), Caret, Grp(F.Id("n")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n, b(n) is the real central-binomial "
                    + "coefficient divided by 4^n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-half-binomial-multichoose"),
                DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialIntegral.b_multichoose"),
                H("The half-parameter multichoose coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n, Ring.multichoose (1/2 : Real) n "
                    + "equals b(n). This coefficient identity supplies the binomial power-series "
                    + "step in the integral representation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-half-binomial-coefficient-nonnegative"),
                DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialIntegral.b_nonneg"),
                H("Nonnegativity of every normalized coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n, 0<=b(n). The central-binomial "
                    + "coefficient is nonnegative and its denominator 4^n is positive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-half-binomial-coefficient-upper-bound"),
                DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialIntegral.b_le_one"),
                H("A uniform upper bound for the normalized coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n, b(n)<=1. The central-binomial "
                    + "bound centralBinom(n)<=4^n gives this estimate, including n=0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-half-binomial-kernel-series"),
                DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialIntegral.binomial_hasSum"),
                H("The square-root kernel as a binomial series"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real u with 0<=u<1, the series with nth "
                    + "term b(n)u^n has sum 1/sqrt(1-u). The parameter is the argument of "
                    + "the binomial series; in the arcsine integral it is t^2, whereas in "
                    + "the elliptic sine integral it is r*sin(theta)^2."))),
                DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("original-half-binomial-elliptic-integral"),
            DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialIntegral.original_series_eq_integral"),
            H("Summability, integrability and the exact identity including zero"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every real r with 0<=r<1, the complex series with nth term "
                    + "halfBinomial(n)^2 times (r:Complex)^n is summable. The real function "
                    + "theta maps to 1/sqrt(1-r*sin(theta)^2) is interval integrable from zero "
                    + "to pi/2, and the sum of that same complex series equals the complex "
                    + "embedding of (2/pi) times that real integral. The original coefficient "
                    + "halfBinomial(n) is the product of (-1/2-j) for 0<=j<n, divided by n!, "
                    + "including its zeroth term and its alternating sign before squaring. No analytic identity or "
                    + "convergence assertion is a hypothesis.")),
                Paragraph(Text("Write b_n=centralBinom(n)/4^n. The original successor law gives "
                    + "halfBinomial(n)=(-1)^n b_n. Mathlib's binomial power series identifies "
                    + "sum b_n u^n with 1/sqrt(1-u) for 0<=u<1. The sine-power reduction "
                    + "formula gives integral from zero to pi/2 of sin(theta)^(2n) equal "
                    + "to (pi/2)b_n. Each term b_n r^n sin(theta)^(2n) is bounded in "
                    + "absolute value by r^n, since 0<=b_n<=1 and sin(theta)^2<=1. "
                    + "The summable geometric bound justifies termwise interval integration. "
                    + "Continuity and the lower bound 1-r>0 give actual integrability of "
                    + "the square-root kernel. Uniqueness of sums and the real-to-complex "
                    + "continuous embedding yield the displayed literal identity.")),
                Paragraph(Text("This is the classical Euler-Gauss representation of the "
                    + "complete elliptic integral, with parameter r and normalization 2/pi. "
                    + "No originality claim is made. The result supplies the analytic bridge "
                    + "needed for complementary-period endpoint estimates; it does not "
                    + "establish the logarithmic constant, the nome, an original Gaussian "
                    + "realization, crossing, string theory or an AdS/CFT correspondence."))),
            DescribeRole.Theorem),
            new DocumentBlock.Section(H("An arcsine application on the closed interval"), Blocks(
            Paragraph(Text("For every natural n define the rational coefficient "
                + "c_n=choose(2n,n)/(4^n(2n+1)), and let a_n be its image in the reals. "
                + "Since centralBinom(n)=choose(2n,n), a_n=b(n)/(2n+1). Thus "
                + "0<=a_n<=1. For every real x with |x|<=1 the series with nth term "
                + "a_n*x^(2n+1) has sum arcsin(x). Both x=1 and x=-1 are included; "
                + "their sums are pi/2 and -pi/2, respectively.")),
            Paragraph(Text("To obtain the endpoint as well as the interior, fix 0<=y<=1 "
                + "and put K(t)=1/sqrt(1-t^2). The function arcsin is continuous on [0,y], "
                + "and for 0<t<y its derivative is K(t)>=0. The interval-integrability "
                + "theorem for a nonnegative derivative therefore makes K integrable "
                + "on 0..y, including y=1. The fundamental theorem of calculus and "
                + "arcsin(0)=0 give the integral of K on 0..y equal to arcsin(y). "
                + "Neither theorem requests a derivative at the upper endpoint.")),
            Paragraph(Text("Set F_n(t)=b(n)*t^(2n) and H(t)=sum_n F_n(t), where H is "
                + "the total infinite-sum function. On 0<t<y the substitution u=t^2 "
                + "satisfies 0<=u<1, so binomial_hasSum identifies the sum with K(t). "
                + "Equality on this open interval transfers interval integrability "
                + "from K to H. Each F_n is continuous and nonnegative, hence "
                + "measurable with |F_n(t)|=F_n(t). Use F_n itself as the nth bound "
                + "in the series dominated-convergence theorem. The bounds are "
                + "summable almost everywhere on (0,y], their total H is integrable, "
                + "and the same binomial series gives the required sum K almost "
                + "everywhere. The only excluded upper endpoint is a null singleton. "
                + "This verifies every premise of termwise integration without "
                + "assuming a binomial-series value at t=1.")),
            Paragraph(Text("Termwise integration gives the nth integral "
                + "b(n)*y^(2n+1)/(2n+1)=a_n*y^(2n+1). Its total is the integral "
                + "of K, hence arcsin(y). This also handles y=0, where the open "
                + "interval is empty and every integrated term is zero. For x<0, "
                + "apply the nonnegative result to -x, negate its HasSum, and use "
                + "arcsin(-x)=-arcsin(x) and the odd exponents. This yields the "
                + "same series on the whole closed interval [-1,1].")))),
            new DocumentBlock.Section(H("Interior truncation and the function A"), Blocks(
            Paragraph(Text("For all real x,q and natural N satisfying 0<=q<1 and "
                + "|x|<=q, write S_N(x)=sum_{0<=n<N} a_n*x^(2n+1). Coefficient "
                + "nonnegativity and a_n<=1 give |a_n*x^(2n+1)|<=q*(q^2)^n. "
                + "The geometric-series remainder theorem with C=q and r=q^2 "
                + "therefore gives |arcsin(x)-S_N(x)|<=q^(2N+1)/(1-q^2). "
                + "The denominator is positive, and the power identity "
                + "q*(q^2)^N=q^(2N+1) uses no division by q. Consequently the "
                + "bound includes q=0 and N=0.")),
            Paragraph(Text("Define A(x)=2*x+2*arcsin(x) and "
                + "A_N(x)=2*x+2*S_N(x). For every |x|<=1, A(x) equals "
                + "2*x+2*sum_n a_n*x^(2n+1). Under the interior assumptions "
                + "0<=q<1 and |x|<=q, cancellation of the 2*x terms gives "
                + "|A(x)-A_N(x)|<=2*q^(2N+1)/(1-q^2). These are classical "
                + "arcsine-series consequences of the normalized binomial kernel. "
                + "The endpoint convergence assertion supplies no endpoint "
                + "truncation rate; the displayed error bounds require q<1.")))))));
}
