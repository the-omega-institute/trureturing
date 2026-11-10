using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233256RowOneDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256RowOne.";
    private const string LeanPrefix = "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233256RowOne.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233256");
    private static DocumentBlock Node(string name, string title, Formula formula,
        bool theorem = false, bool literature = false, bool resolution = false) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source)
                : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(title + "."))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition,
            resolution ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("hardin233256-rowone"), ResolutionKind.Proved) : null);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hardin's RowOne recurrence for literal normalized six-colour arrays.",
        H("A233256 RowOne"),
        Blocks(
            Paragraph(Text("A one-row array is a path. Its adjacent cells exclude equal colours and colours summing to five. Transposition preserves its ordered cells and turns it into a width-one row transfer. After one initial continuation step, the reachable state vectors satisfy (t-2)(t-4). The index bound is essential: at width three the proposed right side would be minus two, while the literal count is three.")),
            Node("Legal", "The literal path conditions", LegalFormula()),
            Node("a", "The literal filtered array count", CountFormula(), literature: true),
            Node("finite_certificate", "Exact initial counts", InitialFormula(), theorem: true),
            Node("result", "The integer recurrence and initial values", ResultFormula(),
                theorem: true, resolution: true))));

    private static Formula CountFormula()
    {
        var n = V("n"); var a = V("A");
        var cells = Product(Fin(D(1)), Fin(n));
        var arrays = Arrow(cells, Fin(D(6)));
        return All("n", Q("Nat"), Eq(Own("a", n), Par(Call("Finset.card",
            Call("Finset.filter", Fn("A", arrays, Own("Legal", a)),
                Typed(Q("Finset.univ"), Call("Finset", arrays)))))));
    }
    private static Formula InitialFormula()
    {
        Formula E(int i, int v) => Eq(Own("a", Num(i)), Num(v));
        return And(E(1, 1), And(E(2, 1), And(E(3, 3), E(4, 10))));
    }
    private static Formula ResultFormula()
    {
        var n = V("n");
        Formula A(int lag) => Typed(Own("a", Sub(n, Num(lag))), Q("Int"));
        var rhs = Sub(Mul(Num(6), A(1)), Mul(Num(8), A(2)));
        return And(All("n", Q("Nat"), Imp(Le(Num(4), n),
            Eq(Typed(Own("a", n), Q("Int")), rhs))), InitialFormula());
    }
    private static Formula Bond(Formula a, Formula b) =>
        And(Ne(a, b), Ne(Add(Val(a), Val(b)), D(5)));
    private static Formula LegalFormula()
    {
        var n = V("n"); var a = V("A"); var j = V("j"); var i = V("i"); var h = V("h");
        Formula At(Formula index) => App(a, Pair(Typed(D(0), Fin(D(1))), index));
        var x = At(j);
        var first = Ex("j", Fin(n), And(Eq(Val(j), D(0)), Eq(x, Typed(D(0), Fin(D(6))))));
        var bonds = All("j", Fin(n), All("h", Lt(Add(Val(j), D(1)), n),
            Bond(x, At(Typed(Call("Fin.mk", Add(Val(j), D(1)), h), Fin(n))))));
        var normal = All("j", Fin(n), And(
            Imp(Or(Eq(x, D(2)), Or(Eq(x, D(3)), Eq(x, D(4)))),
                Ex("i", Fin(n), And(Lt(i, j), Eq(At(i), D(1))))),
            Imp(Eq(x, D(3)), Ex("i", Fin(n), And(Lt(i, j), Eq(At(i), D(2)))))));
        return All("n", Q("Nat"), All("A", Arrow(Product(Fin(D(1)), Fin(n)), Fin(D(6))),
            Eq(Own("Legal", a), And(first, And(bonds, normal)))));
    }
    private static Formula WidthLegal(Formula a, int k)
    {
        var row = Arrow(Fin(Num(k)), Fin(D(6)));
        var c = V("c"); var d = V("d");
        Formula At(Formula f, int j) => App(f, Typed(Num(j), Fin(Num(k))));
        var r = k == 1 ? Fn("_", row, Q("True"))
            : Fn("c", row, Bond(At(c, 0), At(c, 1)));
        var e = k == 1 ? Fn("_", row, Fn("_", row, Q("True")))
            : Fn("c", row, Fn("d", row, Bond(At(c, 1), At(d, 0))));
        return Call("D5.S3.Combinatorics.TraceAvoidingArrays."
            + "HardinA233251TriangleStrip.widthLegal", r, e, a);
    }
    private static Formula Pair(Formula a, Formula b) => Par(Seq(a, Comma, Sp, b));
    private static Formula Product(Formula a, Formula b) => Seq(Par(a), Sp, Times, Sp, Par(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Par(a), FormulaBinaryOperator.Add, Par(b));
    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { NamePart(part) } : new[] { Dot, NamePart(part) }).ToArray());
    private static Formula NamePart(string name)
    {
        var words = name.Split('_');
        Formula result = V(words[^1]);
        for (var i = words.Length - 2; i >= 0; --i)
            result = Seq(V(words[i]), Underscore, Grp(result));
        return Seq(Operatorname, Grp(result));
    }
    private static Formula Own(string name, params Formula[] args) => Call(LeanPrefix + name, args);
    private static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula x, Formula type) => Par(Seq(x, Colon, Sp, type));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Val(Formula x) => Call("Fin.val", x);
    private static Formula Fn(string name, Formula type, Formula body) =>
        Par(Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Par(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Par(body));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Or, Par(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Par(a), FormulaBinaryOperator.Subtract, Par(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Par(a), FormulaBinaryOperator.Multiply, Par(b));
}
