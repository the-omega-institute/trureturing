using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Brooks;

internal sealed class CutsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Brooks/Cuts.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite connected graph separated by one vertex splits into two connected pieces sharing that vertex.",
        H("Components and Vertex Cuts"),
        Blocks(
            Paragraph(Text(
                "Induce(G,S) is the induced graph on the vertex subset S. Component(H,v) "
                + "denotes the connected component of v in H, and Reachable(H,u,v) means "
                + "that H contains a finite walk between the two vertices. Connectedness "
                + "includes a nonempty vertex type. Accordingly, a disconnected induced "
                + "graph supplies two unreachable vertices only when its vertex set is "
                + "also known to be nonempty.")),
            Describe.Lean(DescribeId.Create("partition-at-cut-vertex"),
                DeclarationHandle.Create(Prefix + "cut_partition_of_unreachable"),
                H("Two Connected Sides of a Cut Vertex"),
                StatementSource.FromAuthor(PartitionFormula()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks")),
                Blocks(Paragraph(Text(
                    "Let G be connected on a finite vertex type with decidable equality. "
                    + "Suppose d and e both differ from x and are unreachable from one "
                    + "another after deleting x. There are disjoint nonempty finite sets "
                    + "A and B, both omitting x, that partition all other vertices. No "
                    + "edge runs between A and B, and each induced graph on A with x "
                    + "adjoined and on B with x adjoined is connected. One side can be "
                    + "chosen as the component of e after deletion; every remaining "
                    + "component attaches to x and belongs to the other side. The two "
                    + "unreachable vertices ensure that neither side is empty."))),
                DescribeRole.Theorem))));

    private static Formula PartitionFormula()
    {
        var v = F.Id("V"); var g = F.Id("G"); var x = F.Id("x");
        var d = F.Id("d"); var e = F.Id("e"); var a = F.Id("A"); var b = F.Id("B");
        var u = F.Id("u"); var w = F.Id("w");
        var noCross = All("u", v, All("w", v, Implies(And(Call("Mem", u, a), Call("Mem", w, b)),
            Not(Call("Adj", g, u, w)))));
        var sides = Exists("A", Call("Finset", v), Exists("B", Call("Finset", v),
            And(Call("Nonempty", a), Call("Nonempty", b), Not(Call("Mem", x, a)),
                Not(Call("Mem", x, b)), Call("Disjoint", a, b),
                Eq(Call("Insert", x, Call("Union", a, b)), Call("Univ", v)), noCross,
                Call("Connected", Call("Induce", g, Call("Insert", x, a))),
                Call("Connected", Call("Induce", g, Call("Insert", x, b))))));
        var premises = And(Call("Connected", g), Ne(d, x), Ne(e, x),
            Not(Call("Reachable", Call("Induce", g, Call("Compl", Call("Singleton", x))), d, e)));
        return Disp(All("V", Call("Type"), Instance("Fintype", v, Instance("DecidableEq", v,
            All("G", Call("SimpleGraph", v), All("x", v, All("d", v, All("e", v,
                Implies(premises, sides)))))))));
    }

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Instance(string name, Formula arg, Formula body) =>
        Seq(OpenBracket, Call(name, arg), CloseBracket, Sp, body);
    private static Formula Eq(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Equal, r);
    private static Formula Ne(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.NotEqual, r);
    private static Formula Not(Formula body) => Seq(Neg, Sp, Open, body, Close);
    private static Formula And(params Formula[] terms)
    {
        var result = terms[^1];
        for (var i = terms.Length - 2; i >= 0; --i)
            result = new Formula.Logic(terms[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Implies(Formula l, Formula r) =>
        new Formula.Logic(Seq(Open, l, Close), FormulaLogicOperator.Implies, Seq(Open, r, Close));
}
