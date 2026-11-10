using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233256ColumnOneDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnOne.";
    private const string LeanPrefix = "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233256ColumnOne.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233256");
    private static DocumentBlock Node(string name, string title, Formula formula,
        bool theorem = false, bool literature = false) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source)
                : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(title + "."))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hardin's ColumnOne recurrence for literal normalized six-colour arrays.",
        H("A233256 ColumnOne"),
        Blocks(
            Paragraph(Text("One column has no horizontal or antidiagonal bonds. The first cell is zero. Each 2, 3 or 4 has a strictly earlier 1, and each 3 a strictly earlier 2. The public row transfer at width one counts these words. Its continuation operator satisfies the polynomial (t-2)(t-4)(t-6); linearity propagates the finite state identity to all lengths.")),
            Node("a", "The literal filtered array count", CountFormula(), literature: true),
            Node("finite_certificate", "Exact initial counts", InitialFormula(), theorem: true),
            Node("result", "The integer recurrence", ResultFormula(),
                theorem: true))));

    private static Formula CountFormula()
    {
        var n = V("n"); var a = V("A");
        var cells = Product(Fin(n), Fin(D(1)));
        var arrays = Arrow(cells, Fin(D(6)));
        return All("n", Q("Nat"), Eq(Own("a", n), Parenthesized(Call("Finset.card",
            Call("Finset.filter", Fn("A", arrays, WidthLegal(a, 1)),
                Typed(Q("Finset.univ"), Call("Finset", arrays)))))));
    }
    private static Formula InitialFormula()
    {
        Formula E(int i, int v) => Eq(Typed(Own("a", Num(i)), Q("Int")), Num(v));
        return And(E(1, 1), And(E(2, 3), And(E(3, 11), E(4, 48))));
    }
    private static Formula ResultFormula()
    {
        var n = V("n");
        Formula A(int lag) => Typed(Own("a", Sub(n, Num(lag))), Q("Int"));
        var rhs = Add(Sub(Mul(Num(12), A(1)), Mul(Num(44), A(2))), Mul(Num(48), A(3)));
        return All("n", Q("Nat"), Imp(Le(Num(4), n),
            Eq(Typed(Own("a", n), Q("Int")), rhs)));
    }
    private static Formula Bond(Formula a, Formula b) =>
        And(Ne(a, b), Ne(Add(Val(a), Val(b)), D(5)));
    private static Formula WidthLegal(Formula a, int k)
    {
        var row = Arrow(Fin(Num(k)), Fin(D(6)));
        var c = V("c"); var d = V("d");
        Formula At(Formula f, int j) => App(f, Typed(Num(j), Fin(Num(k))));
        var r = k == 1 ? Call("Function.const", row, Q("True"))
            : Fn("c", row, Bond(At(c, 0), At(c, 1)));
        var e = k == 1 ? Call("Function.const", row, Call("Function.const", row, Q("True")))
            : Fn("c", row, Fn("d", row, Bond(At(c, 1), At(d, 0))));
        return Call("D5.S3.Combinatorics.TraceAvoidingArrays."
            + "HardinA233251TriangleStrip.widthLegal", r, e, a);
    }
    private static Formula Product(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
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
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula x, Formula type) => Parenthesized(Seq(x, Colon, Sp, type));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Val(Formula x) => Call("Fin.val", x);
    private static Formula Fn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
}
