using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor;

internal sealed class SmoothPredecessorGroupStateDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/GroupState.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/makowskischinzel1964totient");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every prefix of a labelled group", H("Every prefix of a labelled group"), Blocks(
            Node("stepTable_group", "Projection of a successful table run", Group(false),
                "Fix a group index i and an initial state (j,L). Filtering a successful " +
                "table run by that label preserves its order, increments the count by " +
                "the number of matching entries, and replaces L by the successive " +
                "integer quotients floor(L(q-1)/q). Every proper prefix passes prefixOk."),
            Node("fixedProduct_le", "Integer products bound rational products from below",
                B(Le(Call("fixedProduct", V("L"), V("qs")),
                    Mul(V("L"), Call("lowerProduct", V("qs")))),
                    ("L", Nat()), ("qs", List(Nat()))),
                "For every finite list of natural numbers q, including zero, rounding down after " +
                "each multiplication gives at most L times the exact rational product " +
                "of (q-1)/q. The lowerProduct notation denotes precisely that product."),
            Node("stepTable_all_prefixes", "Terminal checks include the last prefix", Group(true),
                "Under a successful run, every prefix passes exactly when its last prefix passes. " +
                "All proper prefixes occur before a transition; no other group is required."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        bool definition = false) => Describe.Lean(
        DescribeId.Create("smooth-predecessor-groupstate-" +
            name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))),
        definition ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula Group(bool all)
    {
        var ts = V("ts"); var es = V("es"); var st = V("st"); var end = V("end");
        var i = V("i"); var p = V("p"); var j = V("j"); var l = V("L"); var t = V("t");
        var qs = Call("groupValues", i, es); var length = Call("length", qs);
        var check = Eq(Call("prefixOk", p, Add(j, V("k")),
            Call("fixedProduct", l, Call("take", V("k"), qs)), t), True());
        var run = Eq(Call("stepTable", ts, es, st), Call("some", end));
        var hp = Eq(Call("lookup", V("oddPrimes"), i), Call("some", p));
        var hs = Eq(Call("lookup", st, i), Call("some", Call("pair", j, l)));
        var ht = Eq(Call("lookup", ts, i), Call("some", t));
        Formula result = all
            ? Then(new Formula.Logic(All("k", Nat(), Imp(Le(V("k"), length), check)),
                FormulaLogicOperator.Iff,
                Eq(Call("prefixOk", p, Add(j, length),
                    Call("fixedProduct", l, qs), t), True())), run, hp, hs, ht)
            : Then(And(Eq(Call("lookup", end, i), Call("some", Call("pair",
                    Add(j, length), Call("fixedProduct", l, qs)))),
                All("k", Nat(), Imp(Lt(V("k"), length), check))), run, hp, hs, ht);

        return B(result, ("ts", List(Triple())), ("es", List(Nat())), ("st", States()),
            ("end", States()), ("i", Nat()), ("p", Nat()), ("j", Nat()), ("L", Nat()),
            ("t", Triple()));
    }
    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula List(Formula a) => Call("List", a);
    private static Formula Pair(Formula a, Formula b) => Call("Pair", a, b);
    private static Formula Triple() => Pair(Nat(), Pair(Nat(), Nat()));
    private static Formula States() => List(Pair(Nat(), Nat()));
    private static Formula True() => V("true");
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula B(Formula body, params (string Name, Formula Type)[] variables)
    {
        for (var i = variables.Length - 1; i >= 0; --i)
            body = All(variables[i].Name, variables[i].Type, body);
        return body;
    }
    private static Formula Then(Formula result, params Formula[] hypotheses)
    {
        for (var i = hypotheses.Length - 1; i >= 0; --i)
            result = Imp(hypotheses[i], result);
        return result;
    }
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
