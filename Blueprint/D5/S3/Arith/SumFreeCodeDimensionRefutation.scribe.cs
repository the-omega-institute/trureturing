using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class SumFreeCodeDimensionRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/SumFreeCodeDimensionRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "First-order sum-freedom on the ternary plane does not determine the dimension "
            + "of the code obtained by adjoining function coordinates to Reed–Muller rows.",
        H("Sum-Free Functions with Different Code Dimensions"),
        Blocks(
            Node("coordinate-space", "Ternary coordinate space", "V", SpaceFormula(),
                "The points are n-tuples over the field with three elements.", DescribeRole.Definition),
            Node("sum-freedom", "Higher-order sum-freedom", "SumFree", SumFreeFormula(),
                "A linearly independent family of s directions parametrizes an affine "
                    + "s-plane without repetitions. The sum of the function over each such "
                    + "plane must be nonzero.", DescribeRole.Definition),
            Node("reduced-monomials", "Reed–Muller monomial indices", "Monomials", MonomialFormula(),
                "Each exponent is at most two and the total degree is at most 2s minus one. "
                    + "The evaluation vectors span the corresponding Reed–Muller space.", DescribeRole.Definition),
            Node("parity-matrix", "Parity-check rows", "parityMatrix", MatrixFormula(),
                "The first rows evaluate all reduced monomials of the indicated degree. "
                    + "The remaining n rows are the coordinate functions of f. Redundant "
                    + "rows leave the kernel unchanged.", DescribeRole.Definition),
            Node("parity-map", "Parity-check linear map", "parityCheck", CheckFormula(),
                "A word is sent to its scalar product with every parity-check row. "
                    + "The code consists of the words sent to zero.", DescribeRole.Definition),
            Node("code-dimension", "Kernel dimension", "codeDim", DimensionFormula(),
                "The code dimension is the dimension over the ternary field of the "
                    + "kernel of this parity-check linear map.", DescribeRole.Definition),
            Node("dimension-independence", "Dimension independence assertion", "claim", ClaimFormula(),
                "At each admissible dimension and order, any two sum-free functions "
                    + "are asserted to give equal code dimensions.", DescribeRole.Definition),
            Node("dimension-refutation", "Dimension independence is false", "result",
                Disp(new Formula.Not(F.Id("claim"))),
                "For n equal to two and s equal to one, take f(x,y) equal to "
                    + "(x squared plus y squared, zero) and g(x,y) equal to "
                    + "(x squared, y squared). Both sums on every affine line are "
                    + "nonzero. Their parity systems reduce to four and five independent "
                    + "rows respectively; explicit right inverses establish surjectivity. "
                    + "Rank–nullity gives code dimensions five and four.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hou-zhao-2026-sum-free-code-dimension"), ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Field() => Call("ZMod", D(3));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Space(Formula n) => Call("V", n);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Over(Formula op, string name, Formula domain, Formula term) =>
        Seq(new Formula.Subscript(op, Seq(F.Id(name), Sp, InMacro, Sp, domain)), Sp, term);

    private static Formula SpaceFormula()
    {
        var n = F.Id("n");
        return Disp(All("n", Nat(), Equal(Space(n), Arrow(Fin(n), Field()))));
    }

    private static Formula SumFreeFormula()
    {
        var n = F.Id("n"); var s = F.Id("s"); var f = F.Id("f");
        var a = F.Id("a"); var u = F.Id("u"); var i = F.Id("i"); var c = F.Id("c");
        var offset = Over(Sum, "i", Fin(s), Mul(Call("c", i), Call("u", i)));
        var total = Over(Sum, "c", Arrow(Fin(s), Field()), Call("f", Add(a, offset)));
        var nonzero = new Formula.Relation(total, FormulaRelationOperator.NotEqual, D(0));
        return Disp(All("n", Nat(), All("s", Nat(), All("f", Arrow(Space(n), Space(n)),
            Iff(Call("SumFree", s, f), All("a", Space(n), All("u", Arrow(Fin(s), Space(n)),
                Imp(Call("LinearIndependent", Field(), u), nonzero))))))));
    }

    private static Formula MonomialFormula()
    {
        var n = F.Id("n"); var s = F.Id("s"); var e = F.Id("e"); var i = F.Id("i");
        var degree = Over(Sum, "i", Fin(n), Call("val", Call("e", i)));
        var set = Seq(OpenBrace, e, Sp, InMacro, Sp, Arrow(Fin(n), Fin(D(3))), Sp, Bar, Sp,
            Leq(degree, Sub(Mul(D(2), s), D(1))), CloseBrace);
        return Disp(All("n", Nat(), All("s", Nat(), Equal(Call("Monomials", n, s), set))));
    }

    private static Formula MatrixFormula()
    {
        var n = F.Id("n"); var s = F.Id("s"); var f = F.Id("f");
        var e = F.Id("e"); var x = F.Id("x"); var i = F.Id("i");
        var power = Seq(Call("x", i), Caret, Grp(Call("val", Call("e", i))));
        var monomial = All("e", Call("Monomials", n, s), All("x", Space(n),
            Equal(Call("parityMatrix", n, s, f, Call("inl", e), x), Over(Prod, "i", Fin(n), power))));
        var coordinate = All("i", Fin(n), All("x", Space(n),
            Equal(Call("parityMatrix", n, s, f, Call("inr", i), x), Call("f", x, i))));
        return Disp(All("n", Nat(), All("s", Nat(), All("f", Arrow(Space(n), Space(n)),
            And(monomial, coordinate)))));
    }

    private static Formula CheckFormula()
    {
        var n = F.Id("n"); var s = F.Id("s"); var f = F.Id("f");
        var w = F.Id("w"); var r = F.Id("r"); var x = F.Id("x");
        var rows = Call("Sum", Call("Monomials", n, s), Fin(n));
        var term = Mul(Call("parityMatrix", n, s, f, r, x), Call("w", x));
        return Disp(All("n", Nat(), All("s", Nat(), All("f", Arrow(Space(n), Space(n)),
            All("w", Arrow(Space(n), Field()), All("r", rows,
                Equal(Call("parityCheck", n, s, f, w, r), Over(Sum, "x", Space(n), term))))))));
    }

    private static Formula DimensionFormula()
    {
        var n = F.Id("n"); var s = F.Id("s"); var f = F.Id("f");
        return Disp(All("n", Nat(), All("s", Nat(), All("f", Arrow(Space(n), Space(n)),
            Equal(Call("codeDim", n, s, f),
                Call("finrank", Field(), Call("ker", Call("parityCheck", n, s, f))))))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n"); var s = F.Id("s"); var f = F.Id("f"); var g = F.Id("g");
        var conclusion = Imp(Call("SumFree", s, f), Imp(Call("SumFree", s, g),
            Equal(Call("codeDim", n, s, f), Call("codeDim", n, s, g))));
        var functions = All("f", Arrow(Space(n), Space(n)), All("g", Arrow(Space(n), Space(n)), conclusion));
        return Disp(Iff(F.Id("claim"), All("n", Nat(), All("s", Nat(),
            Imp(Leq(D(2), n), Imp(Leq(D(1), s), Imp(Leq(s, Sub(n, D(1))), functions)))))));
    }
}
