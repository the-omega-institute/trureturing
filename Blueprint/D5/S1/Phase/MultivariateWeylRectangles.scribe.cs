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
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Fourier/yifrach2025weyl")),
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
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Fourier/yifrach2025weyl")),
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
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("monomial-curve-equidistribution"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/MultivariateWeylRectangles.monomial_curve_equidistribution"),
                H("A common integer parameter for all input coordinates"),
                StatementSource.FromAuthor(CurveLimit()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Fourier/yifrach2025weyl")),
                Blocks(
                    Paragraph(Text(
                        "For the same irrational alpha and injective nonzero exponent family, "
                        + "let B >= 2 be strictly larger than every exponent digit e(j)(i). "
                        + "Set n(t)(i) = t^(B^i), using i = 0,...,d-1. The averages for "
                        + "t = 1,...,L of every continuous complex observable converge to "
                        + "normalized Haar measure.")),
                    Paragraph(Text(
                        "The degree assigned to e(j) is the finite sum of e(j)(i) B^i. "
                        + "Uniqueness of fixed-length base-B expansions makes these degrees "
                        + "distinct, and nonzero exponent vectors make them positive. "
                        + "Evaluating every input monomial on n(t) gives exactly t to this "
                        + "encoded degree. The one-dimensional shifted rectangle conclusion "
                        + "then supplies sampling from one instead of zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("monomial-curve-visits"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/MultivariateWeylRectangles.monomial_curve_visits"),
                H("Open-set visits beyond every input threshold"),
                StatementSource.FromAuthor(Visit()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Fourier/yifrach2025weyl")),
                Blocks(
                    Paragraph(Text(
                        "Assume d > 0 and that every input monomial occurs in the exponent "
                        + "family. A base larger than all digits is then at least two. For "
                        + "every nonempty open U in the torus and every natural T, there is "
                        + "t >= max(T,1) such that x(n(t)) belongs to U and all n(t)(i) >= T.")),
                    Paragraph(Text(
                        "A nonnegative continuous function supported in U and positive at one "
                        + "point has positive Haar integral. If a tail of the curve avoided U, "
                        + "its Cesaro averages would instead converge to zero, contradicting "
                        + "the preceding limit. Positive integer weights imply t^(B^i) >= t "
                        + "for t >= 1, giving all coordinate bounds at the same visit."))),
                DescribeRole.Theorem))));

    private static Formula CurveLimit() => F.Disp(F.Seq(
        F.Lim, F.Underscore, F.Grp(F.Id("L"), F.To, F.Infty), F.Sp,
        new Formula.Fraction(F.Seq(F.Sum, F.Underscore,
            F.Grp(F.Id("t"), F.Eq, F.D(1)), F.Caret, F.Grp(F.Id("L")), F.Sp,
            F.Id("F"), F.Open, F.Id("x"), F.Open, F.Id("n"), F.Open,
            F.Id("t"), F.Close, F.Close, F.Close), F.Id("L")),
        F.Eq, F.Int, F.Sp, F.Id("F"), F.Sp, F.Id("d"), F.Mu));

    private static Formula Visit() => F.Disp(F.Seq(
        F.Forall, F.Sp, F.Id("T"), F.Comma, F.Sp, F.Exists, F.Sp,
        F.Id("t"), F.Geq, F.Id("max"), F.Open, F.Id("T"), F.Comma, F.D(1), F.Close,
        F.Comma, F.Sp, F.Id("x"), F.Open, F.Id("n"), F.Open, F.Id("t"), F.Close, F.Close,
        F.InMacro, F.Id("U"), F.Comma, F.Sp, F.Forall, F.Sp, F.Id("i"), F.Comma, F.Sp,
        F.Id("n"), F.Open, F.Id("t"), F.Close, F.Underscore, F.Grp(F.Id("i")),
        F.Geq, F.Id("T")));

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
