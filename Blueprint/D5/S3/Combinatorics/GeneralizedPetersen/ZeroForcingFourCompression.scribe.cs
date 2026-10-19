using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GeneralizedPetersen;

internal sealed class ZeroForcingFourCompressionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingFourCompression.";

    public DocumentDefinition Create()
    {
        var m = V("m"); var n = V("n"); var t = V("t");
        var x = V("X"); var y = V("Y"); var u = V("u"); var v = V("v"); var d = V("d");
        var old = Add(m, Num(1));
        var inserted = Pair(Call("fst", v), Call("succAbove", t, Call("snd", v)));
        var buffer = Q(Imp(And(Mem(v, x), Le(d, Num(4))),
            And(Ne(Call("snd", v), Add(t, Call("ofNat", n, d))),
                Ne(Call("snd", v), Sub(t, Call("ofNat", n, d))))),
            ("v", Vertices(n)), ("d", Nat()));
        var incident = Q(Imp(Mem(u, y), Iff(
            Call("Adj", Call("gp", m, Num(4)), u, v),
            Call("Adj", Call("gp", old, Num(4)), Call("insertVertex", t, u),
                Call("insertVertex", t, v)))), ("u", Vertices(m)), ("v", Vertices(m)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Deleting the middle of nine empty cyclic columns preserves selected neighborhoods and the external boundary in P(n,4). The symbolic compression argument follows Wenlin Zhang and Haobo Ma.",
            H("Radius-Four Column Compression"),
            Blocks(
                Node("insertion", "Insert a missing column", "insertVertex",
                    Disp(Q(Eq(Call("insertVertex", t, v), inserted),
                        ("m", Nat()), ("t", Fin(old)), ("v", Vertices(m)))),
                    "The order-preserving insertion acts on the column index and preserves the layer.", DescribeRole.Definition),
                Node("empty-buffer", "A nine-column empty buffer", "EmptyBuffer",
                    Disp(Q(Nonzero(n, Q(Iff(Call("EmptyBuffer", t, x), buffer),
                        ("t", Fin(n)), ("X", Fs(Vertices(n))))), ("n", Nat()))),
                    "The center and the four columns on either cyclic side contain no selected vertex. The condition applies at every cyclic position, including either end of the chosen numbering.", DescribeRole.Definition),
                Node("buffered-deletion", "Exact neighborhood and boundary transport", "buffered_deletion",
                    Disp(Q(Nonzero(m, Q(Imp(And(Le(Num(108), m), Call("EmptyBuffer", t, x)),
                        Ex("Y", Fs(Vertices(m)), And(
                            Eq(Card(y), Card(x)), Eq(Card(Boundary(m, y)), Card(Boundary(old, x))),
                            Eq(Image(y, "v", Call("insertVertex", t, v)), x),
                            Eq(Image(Boundary(m, y), "v", Call("insertVertex", t, v)), Boundary(old, x)),
                            Eq(Image(Call("columns", y), "i", Call("succAbove", t, V("i"))), Call("columns", x)),
                            incident))),
                        ("t", Fin(old)), ("X", Fs(Vertices(old))))), ("m", Nat()))),
                    "Every selected incident edge is preserved in both directions: outer steps of one, inner steps of four, and spokes. Every old neighbor survives, and each new neighbor has a unique old lift. Insertion recovers the entire selected set, external boundary, and column support, so both cardinalities are equal.", DescribeRole.Theorem),
                Node("compression", "Compress a hypothetical small-boundary set to 108 columns", "compression_to_108",
                    Disp(Q(Imp(And(Le(Num(109), n), Eq(Card(x), Num(16)), Le(Card(Boundary(n, x)), Num(9))),
                        Ex("Y", Fs(Vertices(Num(108))), And(Eq(Card(y), Num(16)),
                            Eq(Card(Boundary(Num(108), y)), Card(Boundary(n, x)))))),
                        ("n", Nat()), ("X", Fs(Vertices(n))))),
                    "Spokes place every unselected vertex of an occupied column in the boundary, giving at most twelve occupied columns. Their nine cyclic translates cover at most 108 possible buffer centers. Above 108 columns a center remains outside that cover. Exact buffered deletion and strong induction reduce to 108, preserving the selected and boundary cardinalities. This implication makes no assumption about finite certificates and proves no finite boundary exclusion or zero forcing number.", DescribeRole.Theorem)),
            []));
    }

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Combinatorics/krishnan2026correction")),
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
    private static Formula Eq(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Equal, r);
    private static Formula Ne(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.NotEqual, r);
    private static Formula Le(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, r);
    private static Formula Mem(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.MemberOf, r);
    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Imp(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Implies, r);
    private static Formula Iff(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Iff, r);
    private static Formula Add(Formula l, Formula r) => new Formula.Binary(l, FormulaBinaryOperator.Add, r);
    private static Formula Sub(Formula l, Formula r) => new Formula.Binary(l, FormulaBinaryOperator.Subtract, r);
    private static Formula Card(Formula value) => Call("card", value);
    private static Formula Fin(Formula value) => Call("Fin", value);
    private static Formula Vertices(Formula n) => Seq(Name("Bool"), Times, Sp, Fin(n));
    private static Formula Fs(Formula value) => Call("Finset", value);
    private static Formula Nonzero(Formula value, Formula body) =>
        Seq(OpenBracket, Call("NeZero", value), CloseBracket, Sp, body);
    private static Formula Pair(Formula l, Formula r) => Seq(Open, l, Comma, Sp, r, Close);
    private static Formula Image(Formula set, string variable, Formula value) =>
        new Formula.SetBuilder(value, V(variable), set);
    private static Formula Boundary(Formula n, Formula set) => Call("externalBoundary", Call("gp", n, Num(4)), set);
}
