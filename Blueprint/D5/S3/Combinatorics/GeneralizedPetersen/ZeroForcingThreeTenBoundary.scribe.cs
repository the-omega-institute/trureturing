using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GeneralizedPetersen;

internal sealed class ZeroForcingThreeTenBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeTenBoundary.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/krishnan2026correction");

    public DocumentDefinition Create()
    {
        var n = V("n"); var x = V("X"); var i = V("i"); var m = V("m");
        var t = V("t"); var y = V("Y"); var v = V("v"); var k = V("k");
        var columns = Call("columns", x);
        var buffer = Q(Imp(And(Mem(v, x), Le(k, Num(3))),
            And(Ne(Second(v), Add(t, Call("ofNat", Add(m, Num(1)), k))),
                Ne(Second(v), Sub(t, Call("ofNat", Add(m, Num(1)), k))))),
            ("v", Vertices(Add(m, Num(1)))), ("k", Nat()));
        var inserted = Pair(First(v), Call("succAbove", t, Second(v)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Bounded gaps, the fourteen-column long-gap case, and deletion through an empty buffer give a uniform isoperimetric bound.",
            H("Every Ten-Vertex Set Has Boundary at Least Eight"),
            Blocks(
            Node("bounded-gaps", "The boundary bound for bounded support gaps", "bounded_gap_boundary",
                Disp(Q(Imp(And(Le(Num(14), n), Eq(Card(x), Num(10)), Le(Num(5), Card(columns)), Le(Card(columns), Num(8)), Q(Le(Call("gapWord", columns, i), Num(7)), ("i", Fin(Card(columns))))), Le(Num(8), Card(Call("externalBoundary", n, x)))), ("n", Nat()), ("X", Fs(Vertices(n))))),
                "For a ten-vertex set with five through eight occupied columns and gaps at most seven, the score bound and the exact exceptional-support intervals give external boundary at least eight.",
                DescribeRole.Theorem),
            Node("buffered-deletion", "Remove one column inside an empty buffer", "buffered_deletion",
                Disp(Q(Imp(And(Le(Num(14), m), buffer), Ex("Y", Fs(Vertices(m)), And(Eq(Card(y), Card(x)), Eq(Card(Call("externalBoundary", m, y)), Card(Call("externalBoundary", Add(m, Num(1)), x))), Eq(Image(y, "v", inserted), x), Eq(Image(Call("externalBoundary", m, y), "v", inserted), Call("externalBoundary", Add(m, Num(1)), x)), Eq(Image(Call("columns", y), "i", Call("succAbove", t, i)), Call("columns", x))))), ("m", Nat()), ("t", Fin(Add(m, Num(1)))), ("X", Fs(Vertices(Add(m, Num(1))))))),
                "If no selected column lies within three cyclic steps of t, deletion of t preserves the selected-set cardinality and external-boundary cardinality. The map sending each column through succAbove t recovers the entire selected set, its external boundary, and its occupied columns.",
                DescribeRole.Theorem),
            Node("ten-boundary", "The uniform ten-vertex boundary inequality", "p3_ten_boundary",
                Disp(Q(Imp(And(Le(Num(14), n), Eq(Card(x), Num(10))), Le(Num(8), Card(Call("externalBoundary", n, x)))), ("n", Nat()), ("X", Fs(Vertices(n))))),
                "Every ten-vertex set in P(n,3), for n at least fourteen, has at least eight external neighbors. Occupied spoke mates handle at least nine columns; bounded gaps, the fourteen-column long-gap bound, and strong induction using buffered deletion handle the remaining supports.",
                DescribeRole.Theorem)),
            []));
    }

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Name(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula V(string name) => F.Id(name);
    private static Formula Num(long value) => new Formula.Number(value);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Q(Formula body, params (string Name, Formula Domain)[] variables)
    {
        for (var i = variables.Length - 1; i >= 0; i--)
            body = new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create(variables[i].Name), variables[i].Domain, body);
        return body;
    }
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Mem(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Card(Formula value) => Call("card", value);
    private static Formula Fin(Formula value) => Call("Fin", value);
    private static Formula Vertices(Formula n) => Seq(Name("Bool"), Times, Sp, Fin(n));
    private static Formula Fs(Formula value) => Call("Finset", value);
    private static Formula Pair(Formula left, Formula right) => Seq(Open, left, Comma, Sp, right, Close);
    private static Formula First(Formula value) => Call("fst", value);
    private static Formula Second(Formula value) => Call("snd", value);
    private static Formula Image(Formula set, string variable, Formula value) =>
        new Formula.SetBuilder(value, V(variable), set);
}
