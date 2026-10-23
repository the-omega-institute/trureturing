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
                + "eventually positive side lengths. In the formulas, BoxAverage is A, "
                + "polynomialPhase is chi, monomialOrbit(alpha,e,a) is the torus map "
                + "defined by these shifted monomials, and HaarIntegral is integration "
                + "against normalized Haar measure. Curve(B,t) has coordinate "
                + "t^(B^i.val); Fin(d) uses indices zero through d-1.")),
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

    private static Formula Word(string value) => F.Id(value);
    private static Formula NumberType(string value) => F.Seq(F.Mathbb, F.Grp(Word(value)));
    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new System.Collections.Generic.List<Formula>
            { F.Operatorname, F.Grp(Word(name)), F.Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i != 0) items.Add(F.Comma);
            items.Add(arguments[i]);
        }
        items.Add(F.Close);
        return F.Seq(items.ToArray());
    }
    private static Formula Apply(Formula function, Formula argument) =>
        F.Seq(function, F.Open, argument, F.Close);
    private static Formula Bound(Formula quantifier, string name, Formula type) =>
        F.Seq(quantifier, F.Sp, F.Open, Word(name), F.Colon, type, F.Close, F.Comma, F.Sp);
    private static Formula All(string name, Formula type) => Bound(F.Forall, name, type);
    private static Formula FinD() => Call("Fin", Word("d"));
    private static Formula TupleType() => F.Seq(FinD(), F.To, F.Sp, NumberType("N"));
    private static Formula Torus() => Call("UnitAddTorus", Word("K"));
    private static Formula Observable() => Call("C", Torus(), NumberType("C"));
    private static Formula Orbit(Formula shift) =>
        Call("monomialOrbit", Word("alpha"), Word("e"), shift);
    private static Formula Curve(Formula time) => Call("Curve", Word("B"), time);
    private static Formula Integral() => Call("HaarIntegral", Word("F"));
    private static Formula FamilyParameters() => F.Seq(
        All("d", NumberType("N")), All("K", Call("Type")),
        F.OpenBracket, Call("Fintype", Word("K")), F.CloseBracket, F.Comma, F.Sp,
        All("alpha", F.Seq(NumberType("R"), F.Setminus, NumberType("Q"))),
        All("e", F.Seq(Word("K"), F.To, F.Sp, Call("Finsupp", FinD(), NumberType("N")))));
    private static Formula FamilyHypotheses() => F.Seq(
        Call("Injective", Word("e")), F.Land, F.Sp,
        F.Open, All("j", Word("K")), Apply(Word("e"), Word("j")),
        F.Neq, F.Sp, F.D(0), F.Close);
    private static Formula DigitHypothesis() => F.Seq(
        F.Open, All("j", Word("K")), All("i", FinD()),
        Apply(Apply(Word("e"), Word("j")), Word("i")), F.Lt, Word("B"), F.Close);

    private static Formula CurveLimit() => F.Disp(F.Seq(
        FamilyParameters(), All("B", NumberType("N")), All("F", Observable()),
        F.Open, FamilyHypotheses(), F.Land, F.Sp, F.D(2), F.Leq, F.Sp, Word("B"),
        F.Land, F.Sp, DigitHypothesis(), F.Close, F.Implies, F.Sp,
        F.Lim, F.Underscore, F.Grp(Word("L"), F.To, F.Infty), F.Sp,
        new Formula.Fraction(F.Seq(F.Sum, F.Underscore,
            F.Grp(Word("t"), F.Eq, F.D(1)), F.Caret, F.Grp(Word("L")), F.Sp,
            Apply(Word("F"), Apply(Orbit(F.D(0)), Curve(Word("t"))))), Word("L")),
        F.Eq, Integral()));

    private static Formula Visit() => F.Disp(F.Seq(
        FamilyParameters(), All("B", NumberType("N")),
        All("U", Call("Set", Torus())), All("T", NumberType("N")),
        F.Open, F.D(0), F.Lt, Word("d"), F.Land, F.Sp, FamilyHypotheses(),
        F.Land, F.Sp, F.Open, All("i", FinD()), Bound(F.Exists, "j", Word("K")),
        Apply(Word("e"), Word("j")), F.Eq, Call("single", Word("i"), F.D(1)), F.Close,
        F.Land, F.Sp, DigitHypothesis(), F.Land, F.Sp,
        Call("IsOpen", Word("U")), F.Land, F.Sp, Call("Nonempty", Word("U")), F.Close,
        F.Implies, F.Sp, Bound(F.Exists, "t", NumberType("N")),
        Call("max", Word("T"), F.D(1)), F.Leq, F.Sp, Word("t"), F.Land, F.Sp,
        Apply(Orbit(F.D(0)), Curve(Word("t"))), F.InMacro, F.Sp, Word("U"),
        F.Land, F.Sp, F.Open, All("i", FinD()), Word("T"), F.Leq, F.Sp,
        Apply(Curve(Word("t")), Word("i")), F.Close));

    private static Formula Cancellation() => F.Disp(F.Seq(
        All("d", NumberType("N")),
        All("alpha", F.Seq(NumberType("R"), F.Setminus, NumberType("Q"))),
        All("Q", Call("MvPolynomial", FinD(), NumberType("Z"))),
        F.D(0), F.Lt, Call("totalDegree", Word("Q")), F.Implies, F.Sp,
        All("epsilon", NumberType("R")), F.D(0), F.Lt, Word("epsilon"), F.Implies, F.Sp,
        Bound(F.Exists, "R", NumberType("N")), F.D(1), F.Leq, F.Sp, Word("R"),
        F.Land, F.Sp, F.Open, All("N", TupleType()),
        F.Open, All("i", FinD()), Word("R"), F.Leq, F.Sp,
        Apply(Word("N"), Word("i")), F.Close, F.Implies, F.Sp,
        new Formula.Norm(Call("BoxAverage", Word("N"),
            Call("polynomialPhase", Word("alpha"), Word("Q")))),
        F.Lt, Word("epsilon"), F.Close));

    private static Formula Equidistribution() => F.Disp(F.Seq(
        FamilyParameters(), All("a", TupleType()), All("F", Observable()),
        F.Open, FamilyHypotheses(), F.Close, F.Implies, F.Sp,
        F.Lim, F.Underscore, F.Grp(Word("N"), F.To, F.Infty), F.Sp,
        Call("BoxAverage", Word("N"), F.Seq(Word("F"), F.Circ, F.Sp, Orbit(Word("a")))),
        F.Eq, Integral()));
}
