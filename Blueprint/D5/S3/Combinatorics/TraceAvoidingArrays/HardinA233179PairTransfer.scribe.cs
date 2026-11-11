using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233179PairTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer.";
    private const string LeanPrefix =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Proper pair-label patterns on a six-row ladder.", H("Six-row column transfer"),
        Blocks(
            Paragraph(Text("A column has six labels in Fin 3. Relabelling the palette gives "
                + "122 orbits of the 729 columns. Fifty orbits have compatible successors. "
                + "The remaining orbits have no successors and are combined into one zero "
                + "state, giving a transfer matrix with 51 states. Compatibility only compares "
                + "rows at distance at most one across consecutive columns.")),
            Node("Proper", "Proper pair-label patterns", ProperFormula(), false),
            Node("L", "The literal pair-label count", CountFormula(), false),
            Node("initial_values", "Initial pair-label counts", InitialFormula(), true),
            Node("recurrence", "The shifted relation for L plus six", RecurrenceFormula(), true),
            Paragraph(Text("Finite column enumeration supplies every transition and initial "
                + "weight. TransferMatrix.cardMatrix gives the count at arbitrary width. "
                + "Twenty-six continuation vectors verify an order-24 vector relation after "
                + "one transition. TransferMatrix.scalarRelationShift propagates that relation. "
                + "Its coefficients sum to one, so adding the constant six preserves it. "
                + "The scalar relation starts at width 27; width 26 is supplied separately "
                + "by the initial values.")))));

    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Automata/hardin2013a233179");

    private static DocumentBlock Node(string name, string title, Formula formula, bool theorem) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(title + "."))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    private static Formula ProperFormula()
    {
        var n = V("n"); var p = V("P"); var j = V("j"); var r = V("r"); var s = V("s");
        var next = Call("Fin.mk", Add(Val(j), D(1)), V("h"));
        var body = All("j", Fin(n), All("h", Lt(Add(Val(j), D(1)), n),
            All("r", Fin(D(6)), All("s", Fin(D(6)), Imp(
                And(Le(Val(r), Add(Val(s), D(1))), Le(Val(s), Add(Val(r), D(1)))),
                Ne(App(p, Pair(r, j)), App(p, Pair(s, next))))))));
        return All("n", Q("Nat"), All("P", Arrow(Cells(n), Fin(D(3))),
            Eq(Own("Proper", p), Parenthesized(body))));
    }

    private static Formula CountFormula()
    {
        var n = V("n"); var p = V("P"); var arrays = Arrow(Cells(n), Fin(D(3)));
        return All("n", Q("Nat"), Eq(Own("L", n), Call("Finset.card",
            Call("Finset.filter", Fn("P", arrays, Own("Proper", p)),
                Typed(Q("Finset.univ"), Call("Finset", arrays))))));
    }

    private static Formula InitialFormula()
    {
        var k = V("k");
        var values = Seq(Bang, OpenBracket,
            N("1458"), Comma, Sp,
            N("23346"), Comma, Sp,
            N("235824"), Comma, Sp,
            N("2986152"), Comma, Sp,
            N("33994188"), Comma, Sp,
            N("409408542"), Comma, Sp,
            N("4791504648"), Comma, Sp,
            N("56948232390"), Comma, Sp,
            N("671408641884"), Comma, Sp,
            N("7950212281224"), Comma, Sp,
            N("93923210426688"), Comma, Sp,
            N("1110971521842576"), Comma, Sp,
            N("13132515793768920"), Comma, Sp,
            N("155290791915166218"), Comma, Sp,
            N("1835954950424998884"), Comma, Sp,
            N("21708106678579996182"), Comma, Sp,
            N("256660237490505696204"), Comma, Sp,
            N("3034643594159596884672"), Comma, Sp,
            N("35879810376487028900160"), Comma, Sp,
            N("424224888649277811420648"), Comma, Sp,
            N("5015800426651629427544760"), Comma, Sp,
            N("59304188625218088516497046"), Comma, Sp,
            N("701180686835907546543927912"), Comma, Sp,
            N("8290387169164139913131170926"), Comma, Sp,
            N("98021089474277074253102673060"), Comma, Sp,
            N("1158948987790395127011466558572"), CloseBracket);
        return All("k", Fin(D(2,6)), Eq(Typed(Own("L", Add(Val(k), D(2))), Q("Int")),
            App(Typed(values, Arrow(Fin(D(2,6)), Q("Int"))), k)));
    }

    private static Formula RecurrenceFormula()
    {
        var n = V("n");
        Formula B(int i) => Add(Typed(Own("L", Add(n, Num(i))), Q("Int")), D(6));
        Formula rhs = Mul(N("7"), B(26));
        rhs = Add(rhs, Mul(N("103"), B(25)));
        rhs = Sub(rhs, Mul(N("365"), B(24)));
        rhs = Sub(rhs, Mul(N("2896"), B(23)));
        rhs = Add(rhs, Mul(N("7168"), B(22)));
        rhs = Add(rhs, Mul(N("32291"), B(21)));
        rhs = Sub(rhs, Mul(N("75471"), B(20)));
        rhs = Sub(rhs, Mul(N("161805"), B(19)));
        rhs = Add(rhs, Mul(N("426135"), B(18)));
        rhs = Add(rhs, Mul(N("333692"), B(17)));
        rhs = Sub(rhs, Mul(N("1225001"), B(16)));
        rhs = Sub(rhs, Mul(N("155206"), B(15)));
        rhs = Add(rhs, Mul(N("1850161"), B(14)));
        rhs = Sub(rhs, Mul(N("363389"), B(13)));
        rhs = Sub(rhs, Mul(N("1524689"), B(12)));
        rhs = Add(rhs, Mul(N("557502"), B(11)));
        rhs = Add(rhs, Mul(N("690388"), B(10)));
        rhs = Sub(rhs, Mul(N("312941"), B(9)));
        rhs = Sub(rhs, Mul(N("166928"), B(8)));
        rhs = Add(rhs, Mul(N("81406"), B(7)));
        rhs = Add(rhs, Mul(N("19997"), B(6)));
        rhs = Sub(rhs, Mul(N("9672"), B(5)));
        rhs = Sub(rhs, Mul(N("906"), B(4)));
        rhs = Add(rhs, Mul(N("420"), B(3)));
        return All("n", Q("Nat"), Eq(B(27), rhs));
    }

    private static Formula N(string digits) => D(digits.Select(c => (byte)(c - '0')).ToArray());
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
    private static Formula Cells(Formula n) => Product(Fin(D(6)), Fin(n));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Product(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
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
