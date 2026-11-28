using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using Fm = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class HexagonalThetaMinimumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Montgomery =
        LibraryNoteRef.Create("D5/L/Fourier/montgomery1988minimal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive and negative vertical contributions give an explicit differential " +
        "margin. Stationarity and strict shear and height comparisons identify the unique " +
        "reduced theta minimum.",
        H("Strict vertical monotonicity and the hexagonal minimum"), Blocks([.. Section0.Entries(), .. Section1.Entries()])));

    private static class Section0
    {
        public static DocumentBlock[] Entries() =>
        [
            Entry("vertical_negative_bound", "Uniform first-row-scale bound", Bound(),
                "Pairing the positive and negative second coordinates expresses " +
                "the weighted sum through positive rows. In the first row, pairing " +
                "the first coordinate m with negative m minus one bounds the " +
                "centered half-translate by one plus the unshifted theta series. " +
                "Every other shifted Gaussian row is bounded by the unshifted " +
                "one because all Fourier coefficients are nonnegative. The " +
                "remaining normalized row tail is bounded by the Gaussian tail " +
                "at eight ninths of the height, hence by one fifteenth. " +
                "The reciprocal-parameter identity bounds theta at t over y " +
                "by the square root of y times theta at y. Since y exceeds " +
                "five sixths, exp of negative pi y is less than one eighth, " +
                "and a geometric sum gives theta at y less than four thirds. " +
                "Using y and its square root both greater than four fifths " +
                "gives the factor ninety-one fifteenths. The weighted series " +
                "converges by comparison with the planar theta series at " +
                "half the temperature. Its term with integer coordinates " +
                "zero and one proves strict positivity.")
        ];

    private static DocumentBlock Entry(string name, string title, Formula formula, string body,
        bool definition = false) => Describe.Lean(
            DescribeId.Create("theta-vertical-tail-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Fourier/HexagonalThetaMinimum." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Montgomery),
            Blocks(Paragraph(Text(body))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula V(string s) => Fm.Id(s);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula All(string s, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, p);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);
    private static Formula NegF(Formula a) => new Formula.Negate(a);
    private static Formula ForTY(Formula p) => All("t", R, All("y", R, p));
    private static Formula Value => Call("verticalNegative", V("t"), V("y"));
    private static Formula Scale => Mul(Mul(Mul(D(2), Pi), V("t")),
        Call("exp", NegF(Mul(Mul(Pi, V("t")),
            Add(V("y"), Div(D(1), Mul(D(4), V("y"))))))));


    private static Formula Bound() => ForTY(Imp(Le(D(1), V("t")),
        Imp(Le(Div(Call("sqrt", D(3)), D(2)), V("y")),
            Lt(Value, Mul(Div(D(9, 1), D(1, 5)), Scale)))));

    }

    private static class Section1
    {
        public static DocumentBlock[] Entries() =>
        [
            Entry("hexagonal_vertical_differential_bound", "Positive differential margin", Margin(),
                "The positive square sum is at least the Gaussian scale times " +
                "twenty pi t over nine. The negative sum is less than the scale " +
                "times ninety-one over fifteen. For t at least one, pi t exceeds " +
                "three. Their difference is greater than the scale times twenty pi t over nine minus " +
                "ninety-one fifteenths; this margin is positive."),
            Entry("height_derivative_pos", "Strict vertical derivative", Derivative(),
                "For t at least one, multiply the first height derivative by y " +
                "squared. Its derivative is y squared times the positive " +
                "differential expression, so the weighted first derivative " +
                "strictly increases. At the hexagonal height it is zero by " +
                "threefold symmetry. It is consequently positive at every larger " +
                "height. For temperatures below one, reciprocal-temperature " +
                "duality multiplies the derivative at reciprocal temperature " +
                "by the positive factor one over t."),
            Entry("hexagonal_height_minimum", "Unique height minimum", HeightMinimum(),
                "The theta function at shear one half is continuous on the closed " +
                "height half-line and has positive derivative in its interior. " +
                "It is strictly increasing, giving both the lower bound and " +
                "the equality classification."),
            Entry("reduced_theta_minimum", "Unique minimum on the reduced half-strip", Reduced(),
                "First decrease theta by increasing the shear to one half. Then " +
                "decrease it by lowering the height to the square root of three " +
                "divided by two. Equality in the combined comparison forces " +
                "equality in both strictly monotone steps. The proof needs only " +
                "the rectangular half-strip hypotheses; the circle condition " +
                "from lattice reduction is unnecessary for this comparison. " +
                "This is the reduced-coordinate conclusion of Montgomery's " +
                "Theorem 1, a literature result with the proof reorganized here.")
        ];

    private static DocumentBlock Entry(string name, string title, Formula formula, string body) =>
        Describe.Lean(DescribeId.Create("hexagonal-theta-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Fourier/HexagonalThetaMinimum." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), (name is "height_derivative_pos" or "hexagonal_height_minimum" or "reduced_theta_minimum"
                ? AssessedProvenance.FromLiterature(Montgomery)
                : AssessedProvenance.FromRepo(Montgomery)),
            Blocks(Paragraph(Text(body))));

    private static Formula V(string s) => Fm.Id(s);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula All(string s, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, p);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Lam(string s, Formula p) =>
        Seq(Open, V(s), Colon, R, Sp, Mapsto, Sp, p, Close);
    private static Formula Height => Div(Call("sqrt", D(3)), D(2));
    private static Formula Theta(Formula t, Formula x, Formula y) => Call("F", t, x, y);
    private static Formula G(Formula t, Formula y) => Theta(t, Div(D(1), D(2)), y);
    private static Formula Hex(Formula t) => G(t, Height);
    private static Formula DOne(Formula y) => Call("deriv", Lam("z", G(V("t"), V("z"))), y);
    private static Formula DTwo => Call("deriv", Lam("b", DOne(V("b"))), V("y"));
    private static Formula ForTY(Formula p) => All("t", R, All("y", R, p));
    private static Formula Margin() => ForTY(Imp(Le(D(1), V("t")), Imp(Le(Height, V("y")),
        Lt(Mul(Call("verticalScale", V("t"), V("y")),
                Sub(Div(Mul(Mul(D(2, 0), Pi), V("t")), D(9)), Div(D(9, 1), D(1, 5)))),
            Add(DTwo, Mul(Div(D(2), V("y")), DOne(V("y"))))))));

    private static Formula Derivative() => ForTY(Imp(Lt(D(0), V("t")),
        Imp(Lt(Height, V("y")), Lt(D(0), DOne(V("y"))))));
    private static Formula HeightMinimum() => ForTY(Imp(Lt(D(0), V("t")),
        Imp(Le(Height, V("y")), And(Le(Hex(V("t")), G(V("t"), V("y"))),
            Iff(Equal(G(V("t"), V("y")), Hex(V("t"))), Equal(V("y"), Height))))));
    private static Formula Reduced() => All("t", R, All("x", R, All("y", R,
        Imp(Lt(D(0), V("t")), Imp(Le(D(0), V("x")), Imp(Le(V("x"), Div(D(1), D(2))),
            Imp(Le(Height, V("y")), And(Le(Hex(V("t")), Theta(V("t"), V("x"), V("y"))),
                Iff(Equal(Theta(V("t"), V("x"), V("y")), Hex(V("t"))),
                    And(Equal(V("x"), Div(D(1), D(2))), Equal(V("y"), Height)))))))))));


    }
}
