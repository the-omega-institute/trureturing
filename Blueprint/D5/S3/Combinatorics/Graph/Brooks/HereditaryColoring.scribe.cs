using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Brooks;

internal sealed class HereditaryColoringDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hereditary average degree at most three and exclusion of four-cliques suffice for a proper three-coloring.",
        H("Coloring Hereditarily Sparse Graphs"),
        Blocks(
            Paragraph(Text(
                "FiniteSimpleGraphs means simple graphs on finite vertex types with "
                + "decidable adjacency. For a finite vertex set S, InducedEdges(G,S) is the "
                + "number of unordered edges of the induced simple graph. Parallel indexed "
                + "owners are not counted here: an application from an indexed edge family "
                + "must first bound its distinct simple edges by its indexed owners. "
                + "CliqueFree(G,4) excludes four pairwise adjacent vertices, and "
                + "Colorable(G,3) asserts a proper coloring with three colors.")),
            Describe.Lean(DescribeId.Create("hereditary-three-colors"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Brooks/HereditaryColoring.hereditary_sparse_three_colorable"),
                H("Hereditary Sparsity and Three Colors"),
                StatementSource.FromAuthor(Disp(All("G", Call("FiniteSimpleGraphs"),
                    Implies(And(All("S", Call("FiniteVertexSets", F.Id("G")),
                            LessEqual(Mul(D(2), Call("InducedEdges", F.Id("G"), F.Id("S"))),
                                Mul(D(3), Call("Card", F.Id("S"))))),
                        Call("CliqueFree", F.Id("G"), D(4))),
                        Call("Colorable", F.Id("G"), D(3)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use strong induction over finite vertex sets. When an induced graph "
                    + "has a vertex with fewer than three neighbors, delete that vertex, "
                    + "apply the induction hypothesis, and reuse the low-degree extension "
                    + "lemma to restore it. Otherwise every degree is at least three. "
                    + "The handshake identity and the assumed edge bound force every degree "
                    + "to equal three. The induced graph inherits four-clique exclusion, "
                    + "so the transplanted Brooks theorem supplies its coloring.")),
                    Paragraph(Text(
                        "The empty graph is included. A hereditary average degree bound "
                        + "allows vertices of degree greater than three before deletion. "
                        + "This graph theorem does not assert that independently colored "
                        + "arithmetic blocks have compatible residues or that their "
                        + "replacement labels satisfy a global covering budget."))),
                DescribeRole.Theorem))));

    private static Formula LessEqual(Formula l, Formula r) => Seq(l, Sp, Leq, Sp, r);
    private static Formula Mul(Formula l, Formula r) => Seq(l, Sp, Cdot, Sp, r);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.And, r);
    private static Formula Implies(Formula l, Formula r) =>
        new Formula.Logic(Seq(Open, l, Close), FormulaLogicOperator.Implies, Seq(Open, r, Close));
}
