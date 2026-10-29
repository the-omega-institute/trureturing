using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PowerSeries;

internal sealed class PositiveNewtonSumsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/wojnar2018a301420");
    private static Formula V(string s) => F.Id(s);
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string s, params Formula[] xs) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, Formula n) => new Formula.Power(P(x), n);
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Pos() => Pow(Nat(), Seq(Plus));
    private static Formula Rat() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Fin() => Call("Fin", D(5));
    private static Formula M() => V("Multiplicity");
    private static Formula SumAt(string i, Formula s, Formula f) =>
        Seq(new Formula.Subscript(Sum, Seq(V(i), InMacro, s)), P(f));
    private static Formula ProdAt(string i, Formula s, Formula f) =>
        Seq(new Formula.Subscript(Prod, Seq(V(i), InMacro, s)), P(f));
    private static Formula Mi() => Call("m", V("i"));
    private static Formula R() => Call("count", V("m"));
    private static Formula BinomialProduct() => ProdAt("i", Fin(),
        Pow(Call("choose", D(5), Add(V("i"), D(1))), Mi()));
    private static Formula UnsignedBody() => Mul(Mul(Div(V("k"), Mul(D(5), R())),
        Div(Call("factorial", R()), ProdAt("i", Fin(), Call("factorial", Mi())))), BinomialProduct());
    private static Formula CoefficientBody() => Mul(UnsignedBody(), Pow(Seq(Minus, D(1)), Add(V("k"), R())));
    private static Formula Numerator() => Sub(D(1), Mul(V("X"), Pow(Add(D(1), V("X")), D(4))));
    private static Formula Denominator() => Mul(Sub(D(1), V("X")), Sub(D(2), Pow(Add(D(1), V("X")), D(5))));
    private static Formula A(Formula n) => Call("a", n);
    private static Formula An(int n) => A(Add(V("n"), (n < 10 ? D((byte)n) : D(1, (byte)(n - 10)))));
    private static Formula RecurrenceBody()
    {
        Formula rhs = Sub(Mul(D(7), An(13)), An(12));
        rhs = Sub(rhs, Mul(D(6), An(11)));
        rhs = Add(rhs, Mul(D(2), An(10)));
        rhs = Sub(rhs, An(9));
        rhs = Add(rhs, Mul(D(4), An(8)));
        rhs = Add(rhs, An(7));
        rhs = Add(rhs, Mul(D(4), An(5)));
        rhs = Add(rhs, Mul(D(2), An(4)));
        rhs = Sub(rhs, An(3));
        rhs = Sub(rhs, Mul(D(5), An(2)));
        rhs = Sub(rhs, Mul(D(4), An(1)));
        rhs = Sub(rhs, A(V("n")));
        return All("n", Pos(), Eqn(An(14), rhs));
    }
    private static DocumentBlock Node(string name, string title, Formula body, string prose,
        bool literature = false, bool theorem = false,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("posnewton-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(Disp(body)),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition, resolution);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict positive monomial coefficients give the rational shifted generating function and the positive-index recurrence for A301420.",
        H("Positive coefficients of the five-data Newton sums"),
        Blocks(
            Paragraph(Text("All series have rational coefficients. Fin(5) is indexed by i = 0,1,2,3,4; "
                + "its coordinate i has weight i+1. Positive sequence indices belong to N with zero excluded. "
                + "X is the series variable, C embeds rational constants, and the inverse is the formal multiplicative inverse. "
                + "The formal log is log(1+X); subst(p,f) substitutes p into f, and rescale(c,f) replaces X by cX.")),
            Node("Multiplicity", "Multiplicity vectors", Eqn(M(), Seq(Fin(), To, Nat())),
                "A vector records one nonnegative multiplicity for each of the five distinct monomial variables."),
            Node("count", "Factor count", All("m", M(), Eqn(R(), SumAt("i", Fin(), Mi()))),
                "The total number r of factors is the unweighted sum of the five multiplicities."),
            Node("degree", "Weighted degree", All("m", M(), Eqn(Call("degree", V("m")),
                SumAt("i", Fin(), Mul(Add(V("i"), D(1)), Mi())))),
                "The five weights are one through five. The factor count is at most this weighted degree."),
            Node("multiplicities", "Monomials of a fixed degree", All("k", Nat(),
                All("m", M(), Seq(V("m"), InMacro, Call("multiplicities", V("k")), Iff,
                    Eqn(Call("degree", V("m")), V("k"))))),
                "The finite set is the union over r from zero through k of the r-factor antidiagonals, filtered by weighted degree k. "
                + "Membership is equivalent to degree(m)=k, so every multiplicity vector occurs once."),
            Node("literalCoefficient", "The literal Girard-Waring coefficient", All("k", Pos(), All("m", M(),
                Eqn(Call("literalCoefficient", V("k"), V("m")), CoefficientBody()))),
                "Equation (2) of Wojnar, Wojnar and Brin, arXiv:1706.08381v2, pp. 3-4, gives this normalized five-data coefficient. "
                + "For a vector of degree k its factor count is positive. The coefficient is attached to a monomial before data values are substituted.", true),
            Node("unsignedCoefficient", "The unsigned weight", All("k", Pos(), All("m", M(),
                Eqn(Call("unsignedCoefficient", V("k"), V("m")), UnsignedBody()))),
                "Removing only the parity sign gives the absolute value of the literal coefficient."),
            Node("positiveCoefficient", "The sequence on positive indices", All("k", Pos(),
                Eqn(Call("positiveCoefficient", V("k")), SumAt("m", Call("multiplicities", V("k")),
                    Call("positivePart", Call("literalCoefficient", V("k"), V("m")))))) ,
                "positivePart(c) means c if c>0 and zero otherwise. This is the strict positive coefficient sum in the NAME and COMMENTS of OEIS A301420. "
                + "Each distinct monomial is filtered separately. No index-zero sequence value is defined.", true),
            Node("positiveSeries", "The shifted series", All("n", Nat(),
                Eqn(Call("coeff", V("n"), V("positiveSeries")), Call("positiveCoefficient", Add(V("n"), D(1))))),
                "The coefficient at degree n is the sequence value at n+1. This shift interprets the entry's offset one."),
            Node("dataSeries", "The data polynomial", Eqn(V("dataSeries"), SumAt("i", Fin(),
                Call("monomial", Add(V("i"), D(1)), Call("choose", D(5), Add(V("i"), D(1)))))),
                "This polynomial is (1+X)^5-1. Its zero constant coefficient permits formal logarithm substitution."),
            Node("unsignedLog", "Unsigned logarithmic aggregate", Eqn(V("unsignedLog"),
                Mul(Seq(Minus, Div(D(1), D(5))), Call("subst", Seq(Minus, V("dataSeries")), Call("log", Rat())))),
                "For every positive k, k times this series coefficient is the sum of unsigned monomial weights. "
                + "Multinomial expansion and the factor-count partition prove the identity in every degree."),
            Node("signedLog", "Signed logarithmic aggregate", Eqn(V("signedLog"),
                Mul(Seq(Minus, Div(D(1), D(5))), Call("subst", Call("rescale", Seq(Minus, D(1)), V("dataSeries")), Call("log", Rat())))),
                "For every positive k, k times this coefficient is the sum of literal coefficients. "
                + "Rescaling contributes (-1)^k and the logarithm contributes the factor-count parity."),
            Node("recurrence", "The order-fourteen relation", All("a", Seq(Pos(), To, Rat()),
                Seq(Call("recurrence", V("a")), Iff, P(RecurrenceBody()))),
                "The displayed relation is the FORMULA-field recurrence of A301420, interpreted at every n at least one. "
                + "It makes no asymptotic claim.", true),
            Node("result", "Generating function and recurrence", Seq(
                Eqn(V("positiveSeries"), Div(Numerator(), Denominator())), Land,
                Call("recurrence", V("positiveCoefficient"))),
                "For any rational c, twice its positive part is |c|+c. The two aggregate logarithms therefore give "
                + "positiveSeries as half the sum of their derivatives. Formal differentiation yields the stated quotient. "
                + "The printed recurrence polynomial is the denominator times 1-X+X^3-X^4+X^5+X^8. "
                + "Multiplication leaves a polynomial of degree at most thirteen; extracting degree n+13 proves the recurrence for all positive n. "
                + "A302764 also asserts the same generating-function family. The coefficient proof here is derived from the literal sum; global proof novelty is unverified.",
                theorem: true, resolution: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a301420-positive-newton-sums"), ResolutionKind.Proved)))));
}
