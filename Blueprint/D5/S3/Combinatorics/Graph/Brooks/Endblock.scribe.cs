using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Brooks;

internal sealed class EndblockDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Brooks/Endblock.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In a finite cubic graph whose every vertex deletion is connected, a separating pair with nonempty complement yields two nonadjacent neighbors whose deletion remains connected.",
        H("A Good Triple from a Two-Vertex Cut"),
        Blocks(
            Describe.Lean(DescribeId.Create("good-triple-from-two-cut"),
                DeclarationHandle.Create(Prefix + "good_triple_of_two_cut"),
                H("The Endblock Case"),
                StatementSource.FromAuthor(TripleFormula()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks")),
                Blocks(Paragraph(Text(
                    "Let G be a simple graph on a finite vertex type with decidable adjacency. "
                    + "Every vertex has degree exactly three, and deleting any one vertex "
                    + "leaves a connected graph. Suppose distinct vertices x and y separate "
                    + "the graph when deleted, and specify a vertex w outside that pair. "
                    + "Then there are vertices v, a, and b such that a and b are distinct "
                    + "nonadjacent neighbors of v and deleting a and b leaves a connected graph.")),
                    Paragraph(Text(
                        "The witness w makes the complement of the separating pair nonempty; "
                        + "disconnectedness alone would also include an empty complement. "
                        + "The hypothesis about every single-vertex deletion explicitly asks "
                        + "for connectedness, including nonemptiness. No separate assumption "
                        + "that G has no four-clique is used in this theorem.")),
                    Paragraph(Text(
                        "Components after deleting x and y attach to the separating vertices. "
                        + "The degree-three constraint limits the attachment possibilities. "
                        + "Choosing suitable neighbors from the separated components gives "
                        + "a nonadjacent pair, and the endblock argument refines the choice "
                        + "so that its deletion preserves connectedness. This good triple "
                        + "provides the geometric input for the cubic coloring argument; "
                        + "the conclusion here is the triple itself."))),
                DescribeRole.Theorem))));

    private static Formula TripleFormula()
    {
        var v = F.Id("V"); var g = F.Id("G"); var x = F.Id("x"); var y = F.Id("y");
        var w = F.Id("w"); var z = F.Id("z"); var t = F.Id("t");
        var a = F.Id("a"); var b = F.Id("b");
        var regular = All("z", v, Rel(Call("degree", g, z), FormulaRelationOperator.Equal, D(3)));
        var noCut = All("z", v, Call("Connected",
            Call("Induce", g, Call("Compl", Call("Singleton", z)))));
        var pair = Call("Pair", x, y);
        var premises = And(regular, noCut, Rel(x, FormulaRelationOperator.NotEqual, y),
            Not(Call("Mem", w, pair)), Not(Call("Connected", Call("Induce", g, Call("Compl", pair)))));
        var conclusion = Exists("t", v, Exists("a", v, Exists("b", v,
            And(Call("Adj", g, t, a), Call("Adj", g, t, b),
                Rel(a, FormulaRelationOperator.NotEqual, b), Not(Call("Adj", g, a, b)),
                Call("Connected", Call("Induce", g, Call("Compl", Call("Pair", a, b))))))));
        return Disp(All("V", Call("Type"), Instance("Fintype", v,
            All("G", Call("SimpleGraph", v), Instance("DecidableRel", Call("Adj", g),
                All("x", v, All("y", v, All("w", v, Implies(premises, conclusion)))))))));
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
    private static Formula Rel(Formula l, FormulaRelationOperator op, Formula r) => new Formula.Relation(l, op, r);
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
