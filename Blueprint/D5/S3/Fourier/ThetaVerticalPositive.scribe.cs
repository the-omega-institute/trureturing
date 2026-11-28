using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using Fm = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class ThetaVerticalPositiveDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Montgomery =
        LibraryNoteRef.Create("D5/L/Fourier/montgomery1988minimal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Threefold integer symmetry forces stationarity at the hexagonal height. Four " +
        "retained directions control the positive square contribution, while the " +
        "second-coordinate Gaussian moment is strictly positive.",
        H("Hexagonal stationarity and vertical contributions"), Blocks([.. Section0.Entries()])));

    private static class Section0
    {
        public static DocumentBlock[] Entries() =>
        [
            Entry("hexTurn", "Integer hexagonal rotation", TurnDefinition(),
                "The bijection sends (m,n) to (n,−m−n), and its inverse sends " +
                "(m,n) to (−m−n,m). It has order three.", true),
            Entry("hex_q_turn", "Preservation of the hexagonal form", TurnInvariant(),
                "Multiplying Q at the hexagonal point by square root three over two " +
                "gives m squared plus mn plus n squared. Substituting the integer " +
                "rotation preserves this polynomial, and hence the original form."),
            Describe.Lean(DescribeId.Create("hexagonal-theta-height-stationary"),
                DeclarationHandle.Create(
                    "D5/S3/Fourier/ThetaVerticalPositive.hexagonal_height_stationary"),
                H("Vanishing height derivative"), StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(Montgomery), Blocks(Paragraph(Text(
                    "Put c equal to the square root of three divided by two. The " +
                    "integer map sending (m,n) to (n,−m−n) is a bijection of order " +
                    "three and preserves the form (m squared plus mn plus n squared) " +
                    "divided by c. The three height derivatives of the quadratic " +
                    "form along each orbit sum to zero. Their Gaussian factors " +
                    "are equal, so the three differentiated Gaussian terms also " +
                    "sum to zero. The height derivative terms are absolutely " +
                    "summable: the absolute value of the height derivative of Q " +
                    "is at most Q divided by y, and the exponential absorbs this " +
                    "linear weight at temperature t divided by two. Reindexing " +
                    "the three sums therefore gives three times the height " +
                    "derivative equal to zero. This proves stationarity for every " +
                    "positive temperature.")))),
            MomentEntry("verticalNegative", "Negative height contribution", Definition(),
                "The weighted Gaussian sum records the square of the second " +
                "integer coordinate. Its coefficient is twice pi times the " +
                "temperature divided by the height.", true),
            MomentEntry("weighted_gaussian_summable", "Weighted convergence", Summability(),
                "The square of the second coordinate is at most the quadratic " +
                "form divided by y. For c equal to pi t over two, the inequality " +
                "u exp of negative u at most one bounds the weighted Gaussian " +
                "by one over c y times the unweighted series at half the " +
                "temperature. Gaussian convergence proves the comparison series " +
                "summable for every positive temperature and height."),
            Entry("verticalPositive", "Positive square contribution", PositiveDefinition(),
                "Each term is a squared height derivative of the quadratic form " +
                "times its positive Gaussian weight. Multiplication by pi t squared " +
                "is the positive part of the second derivative expression.", true),
            Entry("verticalScale", "Shortest-direction Gaussian scale", ScaleDefinition(),
                "The scale uses the Gaussian length y plus one over four y and " +
                "the positive factor two pi t.", true),
            Entry("verticalPositive_lower", "Four-direction lower bound", PositiveLower(),
                "Retain precisely (1,0), (−1,0), (0,1), and (0,−1). All other " +
                "square summands are nonnegative. The retained contribution divided " +
                "by the Gaussian scale is P one plus P two, where P one is pi t " +
                "divided by y to the fourth times exp of pi t times y minus three " +
                "over four y. Its derivative has the sign of pi t times the sum " +
                "of y squared and three quarters, minus four y. When pi t is at " +
                "least four divided by square root three, completing the square makes this derivative " +
                "nonnegative above the hexagonal height. Thus P one increases " +
                "and is at least " +
                "sixteen pi t over nine. The condition y squared at least three " +
                "quarters gives P two at least four pi t over nine. Their sum " +
                "gives the stated twenty pi t over nine lower bound. Summability " +
                "follows from the quadratic Taylor bound for exp: the square " +
                "weight is absorbed by the Gaussian at temperature t over two."),
            Entry("vertical_differential_identity", "Vertical differential identity", Differential(),
                "The second Gaussian height derivative contains the square of the " +
                "first quadratic derivative and a term involving the second quadratic " +
                "derivative. Adding twice the first theta derivative divided by y " +
                "cancels the contribution of the shifted first coordinate. The " +
                "remaining negative contribution is twice pi t divided by y times " +
                "the second-coordinate Gaussian moment. Absolute convergence of " +
                "the square terms, first derivative terms and second-coordinate " +
                "moments permits the sums to be combined.")
        ];

    private static DocumentBlock Entry(string name, string title, Formula formula, string body,
        bool definition = false) => Describe.Lean(
            DescribeId.Create("theta-vertical-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Fourier/ThetaVerticalPositive." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Montgomery),
            Blocks(Paragraph(Text(body))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula V(string s) => Fm.Id(s);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Z => Seq(Mathbb, Grp(V("Z")));
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula All(string s, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, p);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);
    private static Formula NegF(Formula a) => new Formula.Negate(a);
    private static Formula Sq(Formula a) => new Formula.Power(a, D(2));
    private static Formula TurnDefinition() => All("v", Call("Prod", Z, Z), Equal(
        Call("hexTurn", V("v")), Call("pair", Call("snd", V("v")),
            Sub(NegF(Call("fst", V("v"))), Call("snd", V("v"))))));
    private static Formula TurnInvariant() => All("v", Call("Prod", Z, Z), Equal(
        Call("Q", Div(D(1), D(2)), C, Call("hexTurn", V("v"))),
        Call("Q", Div(D(1), D(2)), C, V("v"))));
    private static Formula P => Mul(Pi, V("t"));
    private static Formula C => Div(Call("sqrt", D(3)), D(2));
    private static Formula M => Call("fst", V("v"));
    private static Formula N => Call("snd", V("v"));
    private static Formula A => Sub(Sq(N), Div(Sq(Add(M, Mul(N, Div(D(1), D(2))))),
        Sq(V("y"))));
    private static Formula Gaussian => Call("exp", NegF(Mul(P,
        Call("Q", Div(D(1), D(2)), V("y"), V("v")))));
    private static Formula ForTY(Formula p) => All("t", R, All("y", R, p));
    private static Formula K => Call("verticalScale", V("t"), V("y"));
    private static Formula PositiveDefinition() => ForTY(Equal(
        Call("verticalPositive", V("t"), V("y")), Mul(Sq(P), Call("tsum",
            Seq(Open, V("v"), Colon, Call("Prod", Z, Z), Sp, Mapsto, Sp,
                Mul(Sq(A), Gaussian), Close)))));
    private static Formula ScaleExponent =>
        NegF(Mul(P, Add(V("y"), Div(D(1), Mul(D(4), V("y"))))));
    private static Formula ScaleDefinition() =>
        ForTY(Equal(K, Mul(Mul(D(2), P), Call("exp", ScaleExponent))));
    private static Formula PositiveLower() => ForTY(Imp(Le(Div(D(4), Call("sqrt", D(3))), P), Imp(Le(C, V("y")),
        Le(Mul(K, Div(Mul(D(2,0), P), D(9))),
            Call("verticalPositive", V("t"), V("y"))))));
    private static Formula HeightFunction => Seq(Open, V("z"), Colon, R, Sp, Mapsto, Sp,
        Call("F", V("t"), Div(D(1), D(2)), V("z")), Close);
    private static Formula FirstDerivative(Formula y) => Call("deriv", HeightFunction, y);
    private static Formula SecondDerivative => Call("deriv",
        Seq(Open, V("b"), Colon, R, Sp, Mapsto, Sp, FirstDerivative(V("b")), Close), V("y"));
    private static Formula Differential() => ForTY(Imp(Lt(D(0), V("t")),
        Imp(Lt(D(0), V("y")), Equal(
            Add(SecondDerivative, Mul(Div(D(2), V("y")), FirstDerivative(V("y")))),
            Sub(Call("verticalPositive", V("t"), V("y")),
                Call("verticalNegative", V("t"), V("y")))))));
    private static Formula Statement() => new Formula.Bind(FormulaQuantifier.ForAll,
        FormulaIdentifier.Create("t"), R, new Formula.Logic(
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, V("t")),
            FormulaLogicOperator.Implies, Equal(Call("deriv",
                Seq(Open, V("y"), Colon, R, Sp, Mapsto, Sp,
                    Call("F", V("t"), Div(D(1), D(2)), V("y")), Close),
                Div(Call("sqrt", D(3)), D(2))), D(0))));
    private static DocumentBlock MomentEntry(string name, string title, Formula formula,
        string body, bool definition = false) => Describe.Lean(
            DescribeId.Create("theta-vertical-moment-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Fourier/ThetaVerticalPositive." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Montgomery),
            Blocks(Paragraph(Text(body))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula Lam(string s, Formula t, Formula p) =>
        Seq(Open, V(s), Colon, t, Sp, Mapsto, Sp, p, Close);
    private static Formula Weighted => Mul(Sq(N), Gaussian);
    private static Formula Summability() => ForTY(Imp(Lt(D(0), V("t")),
        Imp(Lt(D(0), V("y")),
            Call("Summable", Lam("v", Call("Prod", Z, Z), Weighted)))));
    private static Formula Definition() => ForTY(Equal(
        Call("verticalNegative", V("t"), V("y")),
        Mul(Div(Mul(Mul(D(2), Pi), V("t")), V("y")),
            Call("tsum", Lam("v", Call("Prod", Z, Z), Weighted)))));


    }
}
