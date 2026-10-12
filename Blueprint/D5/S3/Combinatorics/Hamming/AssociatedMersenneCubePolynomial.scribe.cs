using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hamming;

internal sealed class AssociatedMersenneCubePolynomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/wei2024associatedmersenne");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cube polynomial of the associated Mersenne graphs is determined by a cleared-denominator generating function.",
        H("Cube polynomials of associated Mersenne graphs"),
        Blocks(
            Paragraph(Text(
                "Wei and Yang, Associated Mersenne graphs, arXiv:2407.08237v1, Section 6, "
                    + "Question 6.3 (page 18), asks verbatim: “What is cube polynomial for Associated "
                    + "Mersenne graph \\mathcal{M}_n?” The graph here uses labelled Boolean words and "
                    + "Hamming-distance-one adjacency.")),
            Node("am-graph", "The associated Mersenne graph", "amGraph", AmGraphFormula(),
                "For each natural number n, amGraph n is the simple graph whose vertices are the admissible Boolean functions on Fin n. Two vertices are adjacent exactly when their Hamming distance is one. The admissibility predicate is the circular run constraint from the source.",
                DescribeRole.Definition, true),
            Node("cube-count", "Induced cube count", "cubeCount", CubeCountFormula(),
                "For natural n and k, cubeCount n k is the cardinality of the finite type of finsets of admissible words whose induced graph is isomorphic to hypercube k.",
                DescribeRole.Definition, true),
            Node("cube-poly", "Cube polynomial", "cubePoly", CubePolyFormula(),
                "The cube polynomial of the associated Mersenne graph at n is the finite polynomial sum of cubeCount n k times X to the kth power, for k from zero through n.",
                DescribeRole.Definition, true),
            Node("x", "The polynomial variable as a constant series", "x", XFormula(),
                "x is the constant power series whose coefficient is the polynomial variable X over the integers.", DescribeRole.Definition),
            Node("z", "The length variable", "z", ZFormula(),
                "z is the power-series variable over the integer polynomial ring.", DescribeRole.Definition),
            Node("amc-den", "The cleared denominator", "amcDen", DenFormula(),
                "The denominator is 1 minus z minus z squared minus x z cubed minus x(1+x) z to the fifth power.", DescribeRole.Definition),
            Node("amc-num", "The cleared numerator", "amcNum", NumFormula(),
                "The numerator is z plus 2z squared plus 3xz cubed plus 5x(1+x) z to the fifth power.", DescribeRole.Definition),
            Node("cube-series", "The cube-counting series", "cubeSeries", CubeSeriesFormula(),
                "The coefficient at positive length n is cubePoly n mapped from natural coefficients to integer coefficients, and the constant coefficient is zero.", DescribeRole.Definition),
            Node("claim", "The cleared-denominator answer", "claim", ClaimFormula(),
                "The source's Question 6.3 is answered by the formal power-series identity AMC-1 in cleared-denominator form.",
                DescribeRole.Definition, false),
            Node("result", "The cube polynomial formula", "result", Disp(Id("claim")),
                "The endpoint-removal characterization, the marked double count, and the weighted block-series resolvent prove the claimed generating function for every natural length.",
                DescribeRole.Theorem, false,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wei-yang-2024-associated-mersenne-cube-polynomial"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula? formula, string prose, DescribeRole role, bool literature = false,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Int() => new Formula.NamedConstant(FormulaIdentifier.Create("Int"));
    private static Formula Id(string name) => F.Id(name);
    private static Formula Qualified(string owner, string name) => Seq(Id(owner), Dot, Id(name));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(name.Contains('.') ? Qualified(name.Split('.')[0], name.Split('.')[1]) : Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(Id("fun"), Sp, Parenthesized(Seq(Id(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);

    private static Formula AmWord(Formula n) =>
        Call("Subtype", Lambda("w", Arrow(Call("Fin", n), Id("Bool")), Call("Admissible", Id("w"))));

    private static Formula GraphIso(Formula left, Formula right) =>
        Call("SimpleGraph.Iso", left, right);

    private static Formula AmGraphFormula()
    {
        var n = Id("n");
        var word = AmWord(n);
        var u = Id("u"); var v = Id("v");
        var adjacency = Iff(
            Call("SimpleGraph.Adj", Call("amGraph", n), u, v),
            Eq(Call("hammingDist", Call("Subtype.val", u), Call("Subtype.val", v)), D(1)));
        return Disp(All("n", Nat(), All("u", word, All("v", word, adjacency))));
    }

    private static Formula CubeCountFormula()
    {
        var n = Id("n"); var k = Id("k");
        var words = AmWord(n);
        var finsets = Call("Finset", words);
        var graph = Call("amGraph", n);
        var s = Id("S");
        var cubes = Call("Nonempty", GraphIso(Call("SimpleGraph.induce", graph, Call("SetLike.coe", s)),
            Call("hypercube", k)));
        var subtype = Call("Subtype", Lambda("S", finsets, cubes));
        return Disp(All("n", Nat(), All("k", Nat(), Eq(
            Call("cubeCount", n, k), Call("Nat.card", subtype)))));
    }

    private static Formula CubePolyFormula()
    {
        var n = Id("n"); var k = Id("k");
        var sum = Seq(Sum, Sp, Parenthesized(Seq(k, Colon, Sp, Nat())), Sp, InMacro, Sp, Call("Finset.range", Parenthesized(Add(n, D(1)))),
            Sp, Comma, Sp, Call("Polynomial.monomial", k, Call("cubeCount", n, k)));
        return Disp(All("n", Nat(), Eq(Call("cubePoly", n), sum)));
    }

    private static Formula XFormula() => Disp(Eq(Id("x"), Call("PowerSeries.C", Qualified("Polynomial", "X"))));
    private static Formula ZFormula() => Disp(Eq(Id("z"), Qualified("PowerSeries", "X")));

    private static Formula DenFormula()
    {
        var x = Id("x"); var z = Id("z");
        return Disp(Eq(Id("amcDen"), Sub(Sub(Sub(Sub(D(1), z), Pow(z, D(2))), Mul(x, Pow(z, D(3)))), Mul(Mul(x, Add(D(1), x)), Pow(z, D(5))))));
    }

    private static Formula NumFormula()
    {
        var x = Id("x"); var z = Id("z");
        return Disp(Eq(Id("amcNum"), Add(Add(Add(z, Mul(D(2), Pow(z, D(2)))), Mul(Mul(D(3), x), Pow(z, D(3)))), Mul(Mul(D(5), Mul(x, Add(D(1), x))), Pow(z, D(5))))));
    }

    private static Formula CubeSeriesFormula()
    {
        var n = Id("n");
        var body = Call("PowerSeries.mk", Lambda("n", Nat(),
            Seq(Id("if"), Sp, Eq(n, D(0)), Sp, Id("then"), Sp, D(0), Sp,
                Id("else"), Sp, Call("Polynomial.map", Call("Nat.castRingHom", Int()), Call("cubePoly", n)))));
        return Disp(Eq(Id("cubeSeries"), body));
    }

    private static Formula ClaimFormula()
    {
        var cs = Id("cubeSeries"); var z = Id("z"); var d = Id("amcDen");
        var left = Mul(Mul(cs, Sub(D(1), Pow(z, D(2)))), d);
        var right = Sub(Mul(Id("amcNum"), Sub(D(1), Pow(z, D(2)))), Mul(Mul(D(2), Pow(z, D(2))), d));
        return Disp(Eq(left, right));
    }
}
