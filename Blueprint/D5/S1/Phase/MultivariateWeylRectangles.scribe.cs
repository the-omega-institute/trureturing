using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase;

internal sealed class MultivariateWeylRectanglesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial phases cancel over rectangles whose sides grow independently; distinct "
        + "nonconstant monomials consequently have Haar averages for continuous observables.",
        H("Polynomial Equidistribution on Unrestricted Rectangles"),
        Blocks(
            Paragraph(Text(
                "For d natural, write B(N) for the tuples n with 0 <= n(i) < N(i), and "
                + "A(N,f) for their normalized complex average. Let chi(alpha,Q,n) be "
                + "exp(2 pi I alpha Q(n)), where Q is an integer polynomial in d variables. "
                + "The average on an empty box is zero; all limit statements concern "
                + "eventually positive side lengths.")),
            Describe.Lean(
                DescribeId.Create("polynomial-rectangular-cancellation"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/MultivariateWeylRectangles.polynomial_rectangular_cancellation"),
                H("One threshold for all rectangular shapes"),
                StatementSource.FromAuthor(Cancellation()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every irrational real alpha and every integer polynomial Q of "
                        + "positive total degree, each positive epsilon admits an integer R >= 1 "
                        + "such that every box with N(i) >= R has |A(N,chi(alpha,Q))| < epsilon. "
                        + "There is no restriction on the ratios of side lengths.")),
                    Paragraph(Text(
                        "Choose a coordinate with nonzero derivative of the highest homogeneous "
                        + "part. Distinct translations in this same coordinate have difference "
                        + "of degree exactly deg(Q)-1, with highest part equal to the translation "
                        + "difference times that derivative. Whole-box Cauchy-Schwarz bounds the "
                        + "smoothed average by the real parts of whole-box correlations. Fixing "
                        + "the finite smoothing length first makes all correlation thresholds "
                        + "simultaneous. The boundary error is at most twice the translation "
                        + "length divided by the chosen side length. Strong induction ends at "
                        + "the phase-independent geometric-sum bound for linear polynomials.")),
                    Paragraph(Text(
                        "This is a formal derivation of the classical Weyl differencing method. "
                        + "No mathematical novelty is asserted. The derivation explicitly treats "
                        + "independently growing rectangles; a theorem stated only for Euclidean "
                        + "balls does not supply this averaging shape."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("monomial-rectangular-equidistribution"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/MultivariateWeylRectangles.monomial_rectangular_equidistribution"),
                H("Continuous observables of shifted monomial families"),
                StatementSource.FromAuthor(Equidistribution()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let K be any finite index type and e:K -> (Fin d -> finite-support N) "
                        + "be injective, with every e(j) nonzero. For every fixed a:Fin d -> N, "
                        + "the j-coordinate of x(n) is alpha times the monomial with exponent "
                        + "e(j), evaluated at n+a, modulo one. For every continuous complex F "
                        + "on (R/Z)^K, A(N,F composed with x) tends to its normalized Haar integral "
                        + "as N tends to infinity in the coordinatewise order.")),
                    Paragraph(Text(
                        "Every nonzero integer character gives a nonconstant integer polynomial: "
                        + "injectivity of e prevents cancellation of its nonzero coefficients. "
                        + "Translation preserves nonconstancy because the opposite translation "
                        + "is its inverse. The preceding cancellation theorem therefore handles "
                        + "all nonzero characters. Fourier density and uniformly bounded "
                        + "averaging operators extend convergence to every continuous observable. "
                        + "No condition requiring the coordinate monomials to occur is needed."))),
                DescribeRole.Theorem))));

    private static Formula Cancellation() => F.Disp(F.Seq(
        F.Forall, F.Sp, F.Id("epsilon"), F.Gt, F.D(0), F.Comma, F.Sp,
        F.Exists, F.Sp, F.Id("R"), F.Geq, F.D(1), F.Comma, F.Sp,
        F.Forall, F.Sp, F.Id("N"), F.Geq, F.Id("R"), F.Comma, F.Sp,
        new Formula.Norm(F.Seq(F.Id("A"), F.Open, F.Id("N"), F.Comma,
            F.Id("chi"), F.Open, F.Alpha, F.Comma, F.Id("Q"), F.Close, F.Close)),
        F.Lt, F.Id("epsilon")));

    private static Formula Equidistribution() => F.Disp(F.Seq(
        F.Lim, F.Underscore, F.Grp(F.Id("N"), F.To, F.Infty), F.Sp,
        F.Id("A"), F.Open, F.Id("N"), F.Comma, F.Id("F"), F.Circ, F.Id("x"), F.Close,
        F.Eq, F.Int, F.Sp, F.Id("F"), F.Sp, F.Id("d"), F.Mu));
}
