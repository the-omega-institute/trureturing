using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor;

internal sealed class SmoothPredecessorCertificateStateDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/CertificateState.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/makowskischinzel1964totient");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Meaning of ordered-table and state checks", H("Meaning of ordered-table and state checks"), Blocks(
            Node("increasingFrom_sound", "The order test gives strict order and a lower endpoint",
                B(Iff(Eq(Call("increasingFrom", V("prev"), V("xs")), True()),
                    And(Call("PairwiseLt", V("xs")),
                        All("x", Nat(), Imp(Call("member", V("x"), V("xs")),
                            Lt(V("prev"), V("x")))))),
                    ("prev", Nat()), ("xs", List(Nat()))),
                "A true increasingFrom check means the entries are strictly increasing " +
                "and every entry exceeds the supplied lower endpoint."),
            Node("stepTable_head", "A successful first transition exposes its checked state",
                Head(),
                "A nonempty successful run identifies a valid label prime p, the current " +
                "group count j and fixed-point product L, and its tail data t. It checks " +
                "prefixOk before replacing that state by (j+1,floor(L(q-1)/q))."),
            Node("stepTable_append", "Chunks compose as optional state transitions",
                B(Eq(Call("stepTable", V("ts"), Call("append", V("as"), V("bs")), V("st")),
                    Call("bind", Call("stepTable", V("ts"), V("as"), V("st")),
                        Call("stepTable", V("ts"), V("bs")))),
                    ("ts", List(Triple())), ("as", List(Nat())), ("bs", List(Nat())),
                    ("st", States())),
                "Processing a concatenation first processes the left chunk. A failed " +
                "transition remains a failure; a successful state starts the right chunk."),
            Node("finalOk_sound", "Terminal group checks are individually available", Final(),
                "The finalOk check is true exactly when prefixOk holds for each index whose prime, state " +
                "and tail data occur in the three corresponding lists."),
            Node("increasingFrom_append", "Ordered concatenation preserves its endpoint",
                B(Eq(Call("increasingFrom", V("prev"),
                        Call("append", V("as"), V("bs"))),
                    Call("and", Call("increasingFrom", V("prev"), V("as")),
                        Call("increasingFrom", Call("getLastD", V("as"), V("prev")), V("bs")))),
                    ("prev", Nat()), ("as", List(Nat())), ("bs", List(Nat()))),
                "The second chunk starts after the last value of the first chunk. For " +
                "an empty first chunk, getLastD retains the original endpoint."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        bool definition = false) => Describe.Lean(
        DescribeId.Create("smooth-predecessor-certificatestate-" +
            name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))),
        definition ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula Head()
    {
        var e = V("e"); var es = V("es"); var st = V("st"); var end = V("end");
        var ts = V("ts"); var p = V("p"); var j = V("j"); var l = V("L"); var t = V("t");
        var label = Call("entryLabel", e); var q = Call("entryValue", e);
        var next = Call("set", st, label,
            Call("pair", Add(j, D(1)), Call("natDiv", Mul(l, Sub(q, D(1))), q)));
        var conclusion = Ands(
            Eq(Call("lookup", V("oddPrimes"), label), Call("some", p)),
            Eq(Call("lookup", st, label), Call("some", Call("pair", j, l))),
            Eq(Call("lookup", ts, label), Call("some", t)),
            Eq(Call("prefixOk", p, j, l, t), True()),
            Eq(Call("stepTable", ts, es, next), Call("some", end)));
        conclusion = Ex("p", Nat(), Ex("j", Nat(), Ex("L", Nat(), Ex("t", Triple(), conclusion))));
        return B(Iff(Eq(Call("stepTable", ts, Call("cons", e, es), st),
                Call("some", end)), conclusion),
            ("ts", List(Triple())), ("e", Nat()), ("es", List(Nat())),
            ("st", States()), ("end", States()));
    }
    private static Formula Final()
    {
        var ts = V("ts"); var st = V("st"); var i = V("i");
        var p = V("p"); var j = V("j"); var l = V("L"); var t = V("t");
        var checks = B(Then(Eq(Call("prefixOk", p, j, l, t), True()),
            Eq(Call("lookup", V("oddPrimes"), i), Call("some", p)),
            Eq(Call("lookup", st, i), Call("some", Call("pair", j, l))),
            Eq(Call("lookup", ts, i), Call("some", t))),
            ("i", Nat()), ("p", Nat()), ("j", Nat()), ("L", Nat()), ("t", Triple()));
        return B(Iff(Eq(Call("finalOk", ts, st), True()), checks),
            ("ts", List(Triple())), ("st", States()));
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
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
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
    private static Formula Ands(params Formula[] terms)
    {
        var result = terms[^1];
        for (var i = terms.Length - 2; i >= 0; --i) result = And(terms[i], result);
        return result;
    }
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
