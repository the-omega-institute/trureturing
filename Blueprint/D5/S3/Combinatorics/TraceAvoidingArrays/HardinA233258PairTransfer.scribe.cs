using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233258PairTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.";
    private const string LeanPrefix = "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233258");
    private static DocumentBlock Node(string name, string title, Formula formula, bool theorem,
        bool literature = false) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source)
                : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(title + "."))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The five-orbit transfer for three-row horizontal and antidiagonal pair patterns.",
        H("Three-row pair patterns"),
        Blocks(
            Paragraph(Text("A column has three labels and no internal bond. Consecutive "
                + "columns c,d satisfy c(r) != d(r) and d(r) != c(r+1) whenever r+1<3. "
                + "The five first-appearance column representatives are 000, 001, 010, "
                + "011 and 012, with orbit sizes 3,6,6,6,6. Their successor matrix is "
                + "[[2,2,2,2,0],[1,1,0,1,1],[1,1,0,0,0],[1,1,1,1,0],[0,0,0,1,1]]. "
                + "After two columns, the weights are [24,24,12,24,12]. Thus L(n+2) "
                + "is the weighted sum of the continuation vector Q^n*1. The vectors "
                + "satisfy Q^5*1 = 2*Q^2*1 - 7*Q^3*1 + 6*Q^4*1. "
                + "TransferMatrix.cardMatrix, tabulatedPowers and scalarRelationShift "
                + "propagate these finite identities to all widths. The constant six "
                + "satisfies the same cubic relation. The width-six identity is checked "
                + "from the displayed initial counts.")),
            Node("Proper", "Proper pair patterns", ProperFormula(), false),
            Node("L", "Literal pair-pattern count", CountFormula(), false),
            Node("initial_values", "Six initial transfer counts", InitialFormula(), true),
            Node("recurrence", "The constant-adjusted cubic relation", RecurrenceFormula(), true))));

    private static Formula ProperFormula()
    {
        var n = V("n"); var p = V("P"); var j = V("j"); var r = V("r"); var s = V("s");
        var next = Typed(Call("Fin.mk", Add(Val(j), D(1)), V("h")), Fin(n));
        var body = All("j", Fin(n), All("h", Lt(Add(Val(j), D(1)), n),
            All("r", Fin(D(3)), All("s", Fin(D(3)), Imp(
                Or(Eq(r, s), Eq(Val(r), Add(Val(s), D(1)))),
                Ne(App(p, Pair(r, j)), App(p, Pair(s, next))))))));
        return All("n", Q("Nat"), All("P", Arrow(Product(Fin(D(3)), Fin(n)), Fin(D(3))),
            Eq(Own("Proper", p), Parenthesized(body))));
    }
    private static Formula CountFormula()
    {
        var n = V("n"); var p = V("P");
        var arrays = Arrow(Product(Fin(D(3)), Fin(n)), Fin(D(3)));
        return All("n", Q("Nat"), Eq(Own("L", n), Parenthesized(Call("Finset.card",
            Call("Finset.filter", Fn("P", arrays, Own("Proper", p)),
                Typed(Q("Finset.univ"), Call("Finset", arrays)))))));
    }
    private static Formula InitialFormula()
    {
        var values = Seq(Bang, OpenBracket, Num(96), Comma, Sp, Num(432), Comma, Sp,
            Num(1944), Comma, Sp, Num(8856), Comma, Sp, Num(40392), Comma, Sp,
            Num(184248), CloseBracket);
        return All("k", Fin(D(6)), Eq(Typed(Own("L", Add(Val(V("k")), D(2))), Q("Int")),
            App(Typed(values, Arrow(Fin(D(6)), Q("Int"))), V("k"))));
    }
    private static Formula RecurrenceFormula()
    {
        var n = V("n");
        Formula B(int i) => Add(Typed(Own("L", Add(n, Num(i))), Q("Int")), D(6));
        return All("n", Q("Nat"), Eq(B(6),
            Add(Sub(Mul(D(6), B(5)), Mul(D(7), B(4))), Mul(D(2), B(3)))));
    }
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Product(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
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
    private static Formula Own(string name, params Formula[] args) =>
        Call(LeanPrefix + name, args);
    private static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    private static Formula App(Formula f, params Formula[] args) =>
        new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula x, Formula type) =>
        Parenthesized(Seq(x, Colon, Sp, type));
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
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
}
