using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class FoldedGridRectangleSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/FoldedGridRectangleSeries.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/barker2020a096222");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual endpoint rectangle counts satisfy both of Barker's generating-function and recurrence conjectures.",
        H("Rectangles in an alternately folded grid"), Blocks(
            Paragraph(Text("OEIS A096222 counts rectangular placements in the array whose sides are powers of two with exponents floor(n/2) and ceiling(n/2). Natural division Nat.div is floor division, so the second exponent is Nat.div(n+1,2). Rectangles at different positions are distinct. All natural indices, including zero, are retained.")),
            Node("a", "Literal endpoint count", CountFormula(),
                "Each filtered product chooses two natural grid-line indices in increasing order, from zero through the side length inclusive. The outer product chooses the horizontal and vertical intervals independently. Thus its elements are exactly ((x0,x1),(y0,y1)) with x0<x1<=r and y0<y1<=s. Its cardinality is the number of placements. The source says: In this sequence we count the rectangles in an a X b array of squares, where a=2^floor(n/2) and b=2^ceiling(n/2).", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("A", "Formal generating series", SeriesFormula(),
                "PowerSeries.mk assigns coefficient a(n), cast to the rationals, at every natural n. This is a formal series over the rationals; no analytic convergence is required.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The complete joint assertion", Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Par(JointFormula()))),
                "Barker's complete Start/End block asserts both the displayed generating function and the integer recurrence for n>3. The latter is precisely 4<=n on natural indices. Both conjuncts concern the same endpoint count. Integer casts precede the signed subtraction.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Both identities hold", Disp(F.Id("claim")),
                "Finset.card_product_filter_lt counts each ordered endpoint pair by a binomial coefficient. Nat.cast_choose_two gives the source's product of triangular numbers. Splitting the half exponents into their two parity cases proves the recurrence by polynomial normalization. Multiplication of A by the denominator gives numerator coefficients 1,-3,-9,24 at indices zero through three and zero thereafter, using that recurrence. The denominator has constant coefficient one and is therefore a unit in PowerSeries Rat; PowerSeries.eq_mul_inv_iff_mul_eq gives the formal quotient. In particular a(0)=1, a(1)=3, a(2)=9 and a(3)=30. The count formula, the conjectural quotient and recurrence, and their existing implementations are attributed in the source note.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("folded-grid-" + (name == "A" ? "series" : name)),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Nat() => Named("Nat");
    private static Formula Rat() => Named("Rat");
    private static Formula Integer() => Named("Int");
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Cast(Formula a, Formula type) => Par(Seq(a, Colon, type));
    private static Formula LambdaOf(string name, Formula type, Formula body) => Par(Seq(LambdaLower, Sp, F.Id(name), Colon, type, Sp, Mapsto, Sp, body));
    private static Formula Let(string name, Formula value, Formula body) => Par(Seq(F.Id("let"), Sp, F.Id(name), Colon, Nat(), Eq, value, Semi, Sp, body));
    private static Formula Product(Formula a, Formula b) => App(Q("Finset", "product"), a, b);
    private static Formula CountFormula()
    {
        Formula n = F.Id("n"), r = F.Id("r"), s = F.Id("s"), p = F.Id("p");
        Formula PairFilter(Formula side)
        {
            var range = App(Q("Finset", "range"), Add(side, D(1)));
            var pairType = Seq(Nat(), Sp, Times, Sp, Nat());
            var less = new Formula.Relation(Seq(p, Dot, D(1)), FormulaRelationOperator.LessThan, Seq(p, Dot, D(2)));
            return App(Q("Finset", "filter"), LambdaOf("p", pairType, less), Product(range, range));
        }
        var body = Let("r", Pow(D(2), App(Q("Nat", "div"), n, D(2))),
            Let("s", Pow(D(2), App(Q("Nat", "div"), Add(n, D(1)), D(2))),
                App(Q("Finset", "card"), Product(PairFilter(r), PairFilter(s)))));
        return Disp(All("n", Nat(), Eqn(Call("a", n), body)));
    }
    private static Formula SeriesFormula() => Disp(Eqn(
        Cast(F.Id("A"), Call("PowerSeries", Rat())),
        App(Q("PowerSeries", "mk"), LambdaOf("n", Nat(), Cast(Call("a", F.Id("n")), Rat())))));
    private static Formula JointFormula()
    {
        Formula x = Q("PowerSeries", "X"), n = F.Id("n");
        var numerator = Add(Sub(Sub(D(1), Mul(D(3), x)), Mul(D(9), Pow(x, D(2)))), Mul(D(2,4), Pow(x, D(3))));
        var denominator = Mul(Mul(Sub(D(1), Mul(D(2), x)), Sub(D(1), Mul(D(4), x))), Sub(D(1), Mul(D(8), Pow(x, D(2)))));
        var inverse = Seq(Par(denominator), Caret, Grp(Seq(Minus, D(1))));
        var gf = Eqn(F.Id("A"), Mul(Par(numerator), inverse));
        Formula Term(Formula i) => Cast(Call("a", i), Integer());
        var recurrence = Eqn(Term(n), Add(Sub(Mul(D(6), Term(Sub(n, D(1)))), Mul(D(4,8), Term(Sub(n, D(3))))), Mul(D(6,4), Term(Sub(n, D(4))))));
        var guard = new Formula.Relation(D(4), FormulaRelationOperator.LessThanOrEqual, n);
        var tail = All("n", Nat(), new Formula.Logic(guard, FormulaLogicOperator.Implies, recurrence));
        return new Formula.Logic(Par(gf), FormulaLogicOperator.And, Par(tail));
    }
}
