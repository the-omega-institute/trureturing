using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hamming;

internal sealed class BadScienceFiveOptimalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hamming/BadScienceFiveOptimality.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Hamming/alborsetal2026badscience");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The displayed five-dimensional bad science matrix maximizes the unit-row functional.",
        H("The exact five-dimensional bad science optimum"),
        Blocks(
            Node("beta", "The bad science functional", "beta", BetaFormula(),
                "Section 1 (arXiv v2, p. 1) says: “The bad science matrix problem [4] is concerned "
                    + "with understanding, for matrices A ∈ ℝⁿˣⁿ whose rows are normalized to have "
                    + "ℓ²-length 1, the size of the quantity” and displays β(A) = 2⁻ⁿ ∑ ‖Ax‖∞ "
                    + "over x ∈ {−1,1}ⁿ. Here Fin n indexes coordinates, Bool indexes each sign, "
                    + "true gives +1, and false gives −1. The norm on Fin n → ℝ is the sup norm.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("unit-rows", "Unit Euclidean rows", "UnitRows", UnitRowsFormula(),
                "Section 1 (arXiv v2, p. 1) requires rows “normalized to have ℓ²-length 1”. "
                    + "For each row the sum of the squares of its real entries is one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("matrix", "The five-dimensional matrix", "Astar", AstarFormula(),
                "Section 1.4 (arXiv v2, p. 3) displays this matrix, including its scalar "
                    + "factor 1/(2√3). The indices 0 through 4 list its rows and columns in order.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The optimality question", "claim", ClaimFormula(),
                "Section 1.4 (arXiv v2, p. 3) asks verbatim: “We do not know whether this matrix "
                    + "is indeed optimal.” Optimality means that every real five-by-five matrix "
                    + "with unit Euclidean rows has beta at most beta Astar. All 32 Boolean "
                    + "functions are counted once, with uniform weight 1/32.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Optimality in dimension five", "result", Disp(ClaimBody()),
                "The maximum is (2 + 3√3)/4. For every antipodal-free subset S of the "
                    + "five-cube, with m vertices and vector sum u, the proof bounds the "
                    + "Euclidean length of u by (2√3 − 2)m + 8 − 4√3. The parity bound "
                    + "handles m at most five, while cube orthogonality and Cauchy–Schwarz "
                    + "handle m at least six. Choose one maximizing row for each vertex "
                    + "with coordinate zero positive, and orient its sign so its row product "
                    + "is nonnegative. The resulting five cells are antipodal-free and "
                    + "their sizes sum to 16. Summing the affine bound gives 8 + 12√3. "
                    + "For Astar, eight vertices have image sup norm 2 and the other 24 "
                    + "have image sup norm √3, attaining the bound. Uniqueness and "
                    + "dimensions at least six remain open.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("albors-et-al-2024-bad-science-matrix-five"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula NatType() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula RealType() => new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Mat(Formula n) => Call("Matrix", Fin(n), Fin(n), RealType());
    private static Formula Qualified(string owner, string name) => Seq(F.Id(owner), Dot, F.Id(name));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(name.Contains('.')
            ? Qualified(name.Split('.')[0], name.Split('.')[1]) : F.Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula IffOf(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Negate(Formula a) => new Formula.Negate(a);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(F.Id(name), Colon, type)), Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);

    private static Formula BetaFormula()
    {
        var n = F.Id("n"); var a = F.Id("A"); var x = F.Id("x"); var j = F.Id("j");
        var signs = LambdaOf("j", Fin(n), Seq(F.Id("if"), Sp,
            new Formula.Apply(x, [j]), Sp, F.Id("then"), Sp, D(1), Sp,
            F.Id("else"), Sp, Negate(D(1))));
        var sum = SumOver("x", new Formula.TypeArrow(Fin(n), F.Id("Bool")),
            new Formula.Norm(Call("Matrix.mulVec", a, signs)));
        var body = new Formula.Binary(Pow(Parenthesized(Pow(D(2), n)), Seq(Negate(D(1)))),
            FormulaBinaryOperator.Multiply, sum);
        return Disp(All("n", NatType(), All("A", Mat(n), Equal(Call("beta", a), body))));
    }

    private static Formula UnitRowsFormula()
    {
        var n = F.Id("n"); var a = F.Id("A"); var i = F.Id("i"); var j = F.Id("j");
        var body = All("i", Fin(n), Equal(SumOver("j", Fin(n),
            Pow(Parenthesized(new Formula.Apply(a, [i, j])), D(2))), D(1)));
        return Disp(All("n", NatType(), All("A", Mat(n), IffOf(Call("UnitRows", a), body))));
    }

    private static Formula AstarFormula()
    {
        var r = Call("Real.sqrt", D(3));
        var table = Seq(Bang, Bang, OpenBracket,
            D(2), Comma, D(2), Comma, D(0), Comma, D(0), Comma, D(2), Semi, Sp,
            Negate(D(2)), Comma, D(2), Comma, D(0), Comma, D(2), Comma, D(0), Semi, Sp,
            Negate(D(2)), Comma, D(0), Comma, D(0), Comma, Negate(D(2)), Comma, D(2), Semi, Sp,
            D(0), Comma, Negate(r), Comma, r, Comma, r, Comma, r, Semi, Sp,
            D(0), Comma, r, Comma, r, Comma, Negate(r), Comma, Negate(r), CloseBracket);
        var scale = new Formula.Fraction(D(1),
            new Formula.Binary(D(2), FormulaBinaryOperator.Multiply, r));
        return Disp(Equal(F.Id("Astar"), Call("HSMul.hSMul", scale, table)));
    }

    private static Formula ClaimFormula()
        => Disp(IffOf(F.Id("claim"), ClaimBody()));

    private static Formula ClaimBody()
    {
        var a = F.Id("A");
        var conclusion = new Formula.Relation(Call("beta", a),
            FormulaRelationOperator.LessThanOrEqual, Call("beta", F.Id("Astar")));
        return All("A", Mat(D(5)), new Formula.Logic(Call("UnitRows", a),
            FormulaLogicOperator.Implies, conclusion));
    }
}
