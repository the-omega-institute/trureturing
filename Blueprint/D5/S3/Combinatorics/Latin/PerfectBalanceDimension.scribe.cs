using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Latin;

internal sealed class PerfectBalanceDimensionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Latin/PerfectBalanceDimension.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/li2026unbalancedlatin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A direct finite-cut proof of the dimension bound for perfectly balanced Latin rectangles.",
        H("Perfect balance forces the Latin-rectangle dimension bound"),
        Blocks(
            Node("array", "Latin rectangles", "LatinRectangle", ArrayFormula(),
                "The carrier consists of arrays A with k rows and n columns, entries in Fin n, injective in every row and every column. The finite square row maps are bijections. Indices and symbols are zero based; adding one to column labels preserves every distance. Positive sizes are imposed by the result, not by the carrier.", true, DescribeRole.Definition),
            Node("positions", "Symbol positions", "positions", PositionsFormula(),
                "The position permutation is the inverse of the bijective row map. Thus A(i,positions(L,i,u)) equals u, and this is exactly the column containing symbol u. The inverse is constructed from row injectivity on the finite carrier, with no assumed coordinate-bijection bridge.", true, DescribeRole.Definition),
            Node("distance", "Pair distance", "pairDistance", DistanceFormula(),
                "Sum the absolute differences of symbol positions across all rows. Rational arithmetic exactly embeds the integer distances and the rational comparison value k(n+1)/3.", true, DescribeRole.Definition),
            Node("imbalance", "Total imbalance", "imbalance", ImbalanceFormula(),
                "The double sum keeps only u less than v, so each unordered pair contributes exactly once. Every contribution is nonnegative; zero imbalance therefore gives the same distance k(n+1)/3 for every distinct pair.", true, DescribeRole.Definition),
            Node("result", "The full dimension bound", "result", ResultFormula(),
                "This is the direct implication in Li–Ganesh, Section 10 open problem (5), for every positive 1 ≤ k ≤ n. The n = 1 case is explicit. For n ≥ 2 choose a first row permutation p and weights a(u)=2 val(p(u))+1−n. Bijection reindexing gives sum a=0 and N=sum a²=n(n²−1)/3. For any coordinate q, the finite-cut identity gives E(q)=−sum over ordered u,v of a(u)a(v)|q(u)−q(v)|=2 sum over cuts of the squared partial weight sum, hence E(q)≥0. In the first row the cut sums are −(j+1)(j+1−n), and Mathlib's rational Faulhaber theorem gives E(p)=n(n⁴−1)/15. Equal pair distances give sum E(q)=k(n+1)N/3. Keeping the first nonnegative row energy yields k(n+1)/3≥(n²+1)/5. For the integer n≥2, (n−2)(n−3)≥0, including the separate n=2 and n=3 cases, yields n≤2k. Column injectivity remains in the original carrier, although the estimate needs only the row bijections. This does not settle the general ℓ1 Kusner conjecture or nonsquare impossibility.", false, DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, bool literature, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("perfect-balance-dimension-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Abs(Formula a) => Seq(Lvert, Sp, a, Sp, Rvert);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, F.Id(name), Colon, Sp, type, Dot, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula size, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id(name), Sp, InMacro, Sp, Fin(size)), Sp, Parenthesized(body));
    private static Formula Sizes(Formula body) => All("k", Nat(), All("n", Nat(), body));
    private static Formula ArrayType() => Seq(Fin(F.Id("k")), Sp, To, Sp,
        Fin(F.Id("n")), Sp, To, Sp, Fin(F.Id("n")));
    private static Formula Carrier() => Call("LatinRectangle", F.Id("k"), F.Id("n"));
    private static Formula WithArray(Formula body) => Sizes(All("L", Carrier(), body));
    private static Formula Position(Formula row, Formula symbol) =>
        Call("val", Call("positions", F.Id("L"), row, symbol));
    private static Formula TargetDistance() => new Formula.Fraction(
        Mul(F.Id("k"), Add(F.Id("n"), D(1))), D(3));

    private static Formula ArrayFormula()
    {
        var rows = All("i", Fin(F.Id("k")), Call("FunctionInjective", Call("A", F.Id("i"))));
        var columns = All("j", Fin(F.Id("n")), Call("FunctionInjective",
            Lambda("i", Fin(F.Id("k")), Call("A", F.Id("i"), F.Id("j")))));
        return Disp(Sizes(Eq(Carrier(), Call("Subtype", Lambda("A", ArrayType(), And(rows, columns))))));
    }
    private static Formula PositionsFormula() => Disp(WithArray(All("i", Fin(F.Id("k")),
        Eq(Call("positions", F.Id("L"), F.Id("i")),
            Call("inverseBijection", Call("val", F.Id("L"), F.Id("i")))))));
    private static Formula DistanceFormula() => Disp(WithArray(All("u", Fin(F.Id("n")),
        All("v", Fin(F.Id("n")), Eq(Call("pairDistance", F.Id("L"), F.Id("u"), F.Id("v")),
            SumOver("i", F.Id("k"), Abs(Sub(Position(F.Id("i"), F.Id("u")),
                Position(F.Id("i"), F.Id("v"))))))))));
    private static Formula ImbalanceFormula() => Disp(WithArray(Eq(Call("imbalance", F.Id("L")),
        SumOver("u", F.Id("n"), SumOver("v", F.Id("n"),
            Call("ite", Lt(F.Id("u"), F.Id("v")),
                Abs(Sub(Call("pairDistance", F.Id("L"), F.Id("u"), F.Id("v")), TargetDistance())), D(0)))))));
    private static Formula ResultFormula() => Disp(Sizes(
        Imp(Lt(D(0), F.Id("k")), Imp(Le(F.Id("k"), F.Id("n")),
            All("L", Carrier(), Imp(Eq(Call("imbalance", F.Id("L")), D(0)),
                Le(F.Id("n"), Mul(D(2), F.Id("k")))))))));
}
