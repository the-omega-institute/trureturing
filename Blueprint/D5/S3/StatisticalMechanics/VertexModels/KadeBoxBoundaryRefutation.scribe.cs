using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.VertexModels;

internal sealed class KadeBoxBoundaryRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/kade2025boxsixvertex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The determinant formula conjectured by Kade for the partition function of the six-vertex model in a box with arrow-reflecting walls is false already for the smallest box: with one pair of horizontal and one pair of vertical spectral lines, crossing parameter 2, spectral parameters 2 and 3 and all boundary parameters 1, the partition function is -400400/81 while the formula gives -7150.",
        H("The box partition function of the six-vertex model is not given by the conjectured determinant"),
        Blocks(
            Node("a", "The weight a", Disp(Equal(Call("a", P, T), Subtract(Times(P, T), Inv(Times(P, T))))),
                "The weight of the two vertices whose arrows run straight through in the same sense, at crossing parameter p and spectral ratio t.",
                "a", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("b", "The weight b", Disp(Equal(Call("b", T), Subtract(T, Inv(T)))),
                "The weight of the two vertices whose arrows run straight through in opposite senses; it is also the building block of the wall weights.",
                "b", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("c", "The weight c", Disp(Equal(Call("c", P), Subtract(P, Inv(P)))),
                "The weight of the two vertices at which the arrows turn.",
                "c", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("vertex", "Vertex weights", VertexFormula(),
                "At the crossing of a horizontal line with parameter x and a vertical line with parameter y the spectral ratio is t = x/y. The weight is a when all four arrows point right and up or all point left and down, b when the horizontal arrows point left and the vertical ones up or the horizontal ones right and the vertical ones down, c when the horizontal arrows point into the crossing and the vertical ones out of it or the reverse, and 0 for the ten configurations that break the ice rule.",
                "vertexWeight", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("left", "Left wall", WallFormula("leftWall", Xi("L"), F.Id("x"), F.Id("right"), F.Id("left"),
                    Times(F.Id("x"), Xi("L")), new Formula.Fraction(F.Id("x"), Times(P, Xi("L")))),
                "A pair of horizontal lines ends at the left wall; the weight is b(x xi_L) when the upper edge points right and the lower edge left, b(x/(p xi_L)) for the reverse, and 0 otherwise.",
                "leftWall", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("right", "Right wall", WallFormula("rightWall", Xi("R"), F.Id("x"), F.Id("left"), F.Id("right"),
                    Times(F.Id("x"), Xi("R")), new Formula.Fraction(Times(F.Id("x"), P), Xi("R"))),
                "A pair of horizontal lines starts at the right wall; the weight is b(x xi_R) when the upper edge points left and the lower edge right, b(x p/xi_R) for the reverse, and 0 otherwise.",
                "rightWall", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("top", "Top wall", WallFormula("topWall", Xi("U"), F.Id("y"), F.Id("down"), F.Id("up"),
                    Times(F.Id("y"), Xi("U")), new Formula.Fraction(Times(F.Id("y"), P), Xi("U"))),
                "A pair of vertical lines starts at the top wall; the weight is b(y xi_U) when the left edge points down and the right edge up, b(y p/xi_U) for the reverse, and 0 otherwise.",
                "topWall", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bottom", "Bottom wall", WallFormula("bottomWall", Xi("D"), F.Id("y"), F.Id("up"), F.Id("down"),
                    Times(F.Id("y"), Xi("D")), new Formula.Fraction(F.Id("y"), Times(P, Xi("D")))),
                "A pair of vertical lines ends at the bottom wall; the weight is b(y xi_D) when the left edge points up and the right edge down, b(y/(p xi_D)) for the reverse, and 0 otherwise.",
                "bottomWall", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rows", "Line parameters", ParamFormula("rowParam", "x"),
                "Counted from the top, the horizontal lines 2i and 2i + 1 carry x_i and 1/x_i; the vertical lines, counted from the left, carry y_j and 1/y_j in the same way.",
                "rowParam", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("cols", "Column parameters", ParamFormula("colParam", "y"),
                "The vertical lines 2j and 2j + 1, counted from the left, carry y_j and 1/y_j.",
                "colParam", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("z", "The box partition function", ZFormula(),
                "A configuration h, v puts an arrow on each of the 2M + 1 segments of every horizontal line (segment 0 at the left wall, segment 2M at the right wall) and of every vertical line (segment 0 at the top wall, segment 2M at the bottom wall); x_i = xs(i) and y_j = ys(j). Its weight is the product of the wall weights of the M pairs of rows and the M pairs of columns and of the weights of the 4M^2 crossings, where the crossing of row r and column s sees the arrows h(r, s), h(r, s + 1) on its left and right and v(s, r), v(s, r + 1) above and below; the partition function is the sum over all configurations.",
                "Z", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("w", "The factor W", Disp(Equal(Call("W", P, F.Id("x"), F.Id("y")),
                    Times(Times(Times(Call("a", P, Times(F.Id("x"), F.Id("y"))), Call("a", P, Inv(Times(F.Id("x"), F.Id("y"))))),
                        Call("a", P, new Formula.Fraction(F.Id("x"), F.Id("y")))), Call("a", P, new Formula.Fraction(F.Id("y"), F.Id("x")))))),
                "The unitarity factor of two crossing pairs of lines.",
                "W", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("flu", "The corner trace at the top left", Disp(Equal(Call("FLU", P, F.Id("x"), Xi("L"), Xi("U")),
                    Add(Times(Call("b", Times(F.Id("x"), Xi("L"))), Call("b", new Formula.Fraction(Times(F.Id("x"), P), Xi("U")))),
                        Times(Call("b", new Formula.Fraction(F.Id("x"), Times(P, Xi("L")))), Call("b", Times(F.Id("x"), Xi("U"))))))),
                "The sum over the two arrow states of the loop through the left and top walls.",
                "FLU", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("fdr", "The corner trace at the bottom right", Disp(Equal(Call("FDR", P, F.Id("y"), Xi("D"), Xi("R")),
                    Add(Times(Call("b", Times(F.Id("y"), Xi("D"))), Call("b", new Formula.Fraction(Times(F.Id("y"), P), Xi("R")))),
                        Times(Call("b", new Formula.Fraction(F.Id("y"), Times(P, Xi("D")))), Call("b", Times(F.Id("y"), Xi("R"))))))),
                "The sum over the two arrow states of the loop through the bottom and right walls.",
                "FDR", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("formula", "The conjectured value", FormulaFormula(),
                "The product over all i, j of (x_i/y_j - y_j/x_i) W(x_i, y_j), divided by the product over i < j of (x_j/x_i - x_i/x_j)(y_i/y_j - y_j/y_i), times the determinant of the M by M matrix with entries c^2 a(x_i y_j) a(1/(x_i y_j)) F^LU(x_i) F^DR(y_j) / ((x_j/y_i - y_i/x_j) W(x_i, y_j)), as printed.",
                "formula", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture", ClaimFormula(),
                "For every M and all complex parameters at which no printed denominator vanishes (p, the x_i, the y_j and the four boundary parameters nonzero, x_j/y_i - y_i/x_j and W(x_i, y_j) nonzero for all i, j, and the factor for every i < j nonzero), the box partition function equals the conjectured value.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Refutation", Disp(new Formula.Not(F.Id("claim"))),
                "Take M = 1, p = 2, x = 2, y = 3 and all four boundary parameters 1. Over the rationals the kernel sums the weights of all 4096 arrow configurations of the box and obtains -400400/81; the rational cast preserves every weight, so the complex partition function at this point is also -400400/81. There W(2, 3) = -4004/81 and 2/3 - 3/2 = -5/6 are nonzero, the product over i < j is empty, and the formula gives -7150.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kade-2025-box-six-vertex-determinant-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("kadebox-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static readonly Formula P = F.Id("p");
    private static readonly Formula T = F.Id("t");
    private static Formula Xi(string wall) => new Formula.Subscript(F.Id("xi"), F.Id(wall));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Inv(Formula value) => new Formula.Fraction(D(1), value);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Sub(string name, string index) => new Formula.Subscript(F.Id(name), F.Id(index));
    private static Formula Ratio(Formula left, Formula right) =>
        Subtract(new Formula.Fraction(left, right), new Formula.Fraction(right, left));

    private static Formula VertexFormula()
    {
        Formula r = F.Id("right"), l = F.Id("left"), u = F.Id("up"), d = F.Id("down");
        return Disp(Seq(
            Equal(Call("vertexWeight", P, T, r, r, u, u), Call("a", P, T)), Comma, Quad,
            Equal(Call("vertexWeight", P, T, l, l, d, d), Call("a", P, T)), Comma, Quad,
            Equal(Call("vertexWeight", P, T, l, l, u, u), Call("b", T)), Comma, Quad,
            Equal(Call("vertexWeight", P, T, r, r, d, d), Call("b", T)), Comma, Quad,
            Equal(Call("vertexWeight", P, T, r, l, u, d), Call("c", P)), Comma, Quad,
            Equal(Call("vertexWeight", P, T, l, r, d, u), Call("c", P)), Comma, Quad,
            Equal(Call("vertexWeight", P, T, F.Id("hl"), F.Id("hr"), F.Id("vt"), F.Id("vb")), D(0)), Sp,
            Named("otherwise")));
    }

    private static Formula WallFormula(string name, Formula xi, Formula parameter, Formula first, Formula second,
        Formula plus, Formula minus)
    {
        return Disp(Seq(
            Equal(Call(name, P, parameter, xi, first, second), Call("b", plus)), Comma, Quad,
            Equal(Call(name, P, parameter, xi, second, first), Call("b", minus)), Comma, Quad,
            Equal(Call(name, P, parameter, xi, F.Id("e"), F.Id("f")), D(0)), Sp, Named("otherwise")));
    }

    private static Formula ParamFormula(string name, string variable)
    {
        Formula i = F.Id("i"), xs = F.Id(variable + "s");
        return Disp(Seq(
            Equal(Call(name, xs, Times(D(2), i)), Sub(variable, "i")), Comma, Quad,
            Equal(Call(name, xs, Add(Times(D(2), i), D(1))), Inv(Sub(variable, "i")))));
    }

    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Args() => Seq(F.Id("M"), Comma, Sp, P, Comma, Sp, F.Id("xs"), Comma, Sp, F.Id("ys"), Comma, Sp,
        Xi("L"), Comma, Sp, Xi("U"), Comma, Sp, Xi("R"), Comma, Sp, Xi("D"));
    private static Formula CallArgs(string name) => Seq(Named(name), Parenthesized(Args()));

    private static Formula ZFormula()
    {
        Formula m = F.Id("M"), i = F.Id("i"), j = F.Id("j"), r = F.Id("r"), s = F.Id("s");
        Formula m2 = Times(D(2), m);
        Formula hType = new Formula.TypeArrow(FinOf(m2), new Formula.TypeArrow(FinOf(Add(m2, D(1))), Named("HArrow")));
        Formula vType = new Formula.TypeArrow(FinOf(m2), new Formula.TypeArrow(FinOf(Add(m2, D(1))), Named("VArrow")));
        Formula twoI = Times(D(2), i), twoIp = Add(Times(D(2), i), D(1));
        Formula twoJ = Times(D(2), j), twoJp = Add(Times(D(2), j), D(1));
        Formula walls = Seq(
            Prod, Underscore, Grp(Member(i, FinOf(m))), Sp,
            Parenthesized(Times(
                Call("leftWall", P, Sub("x", "i"), Xi("L"), Call("h", twoI, D(0)), Call("h", twoIp, D(0))),
                Call("rightWall", P, Sub("x", "i"), Xi("R"), Call("h", twoI, m2), Call("h", twoIp, m2)))), Sp,
            Prod, Underscore, Grp(Member(j, FinOf(m))), Sp,
            Parenthesized(Times(
                Call("topWall", P, Sub("y", "j"), Xi("U"), Call("v", twoJ, D(0)), Call("v", twoJp, D(0))),
                Call("bottomWall", P, Sub("y", "j"), Xi("D"), Call("v", twoJ, m2), Call("v", twoJp, m2)))));
        Formula cross = Seq(Prod, Underscore, Grp(Member(Seq(r, Comma, s), FinOf(m2))), Sp,
            Call("vertexWeight", P, new Formula.Fraction(Call("rowParam", F.Id("xs"), r), Call("colParam", F.Id("ys"), s)),
                Call("h", r, s), Call("h", r, Add(s, D(1))), Call("v", s, r), Call("v", s, Add(r, D(1)))));
        return Disp(Equal(CallArgs("Z"),
            Seq(Sum, Underscore, Grp(Seq(Member(F.Id("h"), hType), Comma, Sp, Member(F.Id("v"), vType))), Sp,
                walls, Sp, cross)));
    }

    private static Formula FormulaFormula()
    {
        Formula m = F.Id("M"), i = F.Id("i"), j = F.Id("j");
        Formula xi = Sub("x", "i"), xj = Sub("x", "j"), yi = Sub("y", "i"), yj = Sub("y", "j");
        Formula range = Member(Seq(i, Comma, j), FinOf(m));
        Formula numerator = Seq(Prod, Underscore, Grp(range), Sp,
            Parenthesized(Seq(Parenthesized(Ratio(xi, yj)), Sp, Call("W", P, xi, yj))));
        Formula denominator = Seq(Prod, Underscore, Grp(Seq(Less(i, j), Comma, Sp, range)), Sp,
            Parenthesized(Ratio(xj, xi)), Sp, Parenthesized(Ratio(yi, yj)));
        Formula entry = new Formula.Fraction(
            Times(Times(Times(Times(new Formula.Power(Call("c", P), D(2)), Call("a", P, Times(xi, yj))), Call("a", P, Inv(Times(xi, yj)))),
                Call("FLU", P, xi, Xi("L"), Xi("U"))), Call("FDR", P, yj, Xi("D"), Xi("R"))),
            Times(Parenthesized(Ratio(xj, yi)), Call("W", P, xi, yj)));
        return Disp(Equal(CallArgs("formula"),
            Seq(new Formula.Fraction(numerator, denominator), Sp, Named("det"), Underscore, Grp(range), Sp,
                Parenthesized(entry))));
    }

    private static Formula ClaimFormula()
    {
        Formula m = F.Id("M"), i = F.Id("i"), j = F.Id("j");
        Formula xi = Sub("x", "i"), xj = Sub("x", "j"), yi = Sub("y", "i"), yj = Sub("y", "j");
        Formula quantifiers = Seq(
            Forall, Sp, Member(m, Seq(Mathbb, Grp(F.Id("N")))), Comma, Sp,
            Forall, Sp, Member(Seq(P, Comma, Xi("L"), Comma, Xi("U"), Comma, Xi("R"), Comma, Xi("D")), Complex()), Comma, Sp,
            Forall, Sp, Member(Seq(F.Id("xs"), Comma, F.Id("ys")), new Formula.TypeArrow(FinOf(m), Complex())), Comma, Sp);
        Formula nonzero = NotEqual(Seq(P, Comma, Xi("L"), Comma, Xi("U"), Comma, Xi("R"), Comma, Xi("D"), Comma, xi, Comma, yj), D(0));
        Formula conditions = Seq(Forall, Sp, Member(Seq(i, Comma, j), FinOf(m)), Comma, Sp,
            And(And(And(nonzero, NotEqual(Ratio(xj, yi), D(0))), NotEqual(Call("W", P, xi, yj), D(0))),
                Implies(Less(i, j), NotEqual(Times(Parenthesized(Ratio(xj, xi)), Parenthesized(Ratio(yi, yj))), D(0)))));
        return Disp(Iff(F.Id("claim"),
            Seq(quantifiers, Implies(conditions, Equal(CallArgs("Z"), CallArgs("formula"))))));
    }
}
