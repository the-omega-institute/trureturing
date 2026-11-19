using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Incidence;

internal sealed class LineGraphReconstructionDocument : IScribeDocumentDefinition
{
    private static Formula Name(string name) =>
        new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Statement()
    {
        var V = F.Id("V");
        var W = F.Id("W");
        var G = F.Id("G");
        var H = F.Id("H");
        var e = F.Id("e");
        var f = F.Id("f");
        var k = F.Id("k");
        var iso = Call("Iso", G, H);
        var degreeG = All("x", V,
            Call("Nontrivial", Call("neighborSet", G, F.Id("x"))));
        var degreeH = All("y", W,
            Call("Nontrivial", Call("neighborSet", H, F.Id("y"))));
        var hypotheses = And(Call("CliqueFree", G, D(3)),
            And(Call("CliqueFree", H, D(3)), And(degreeG, degreeH)));
        var lift = Exists("f", iso, And(Eq(Call("lineGraph", f), e),
            All("k", iso, Imp(Eq(Call("lineGraph", k), e), Eq(k, f)))));
        return All("u", Name("Level"), All("v", Name("Level"),
            All("V", Call("Type", F.Id("u")), All("W", Call("Type", F.Id("v")),
                All("G", Call("SimpleGraph", V), All("H", Call("SimpleGraph", W),
                    Imp(hypotheses,
                        All("e", Call("Iso", Call("lineGraph", G), Call("lineGraph", H)),
                            lift))))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A prescribed isomorphism of line graphs determines exactly one isomorphism of their triangle-free roots when every vertex has two distinct neighbors.",
        H("Reconstructing vertices from incident edges"),
        Blocks(Describe.Lean(
            DescribeId.Create("unique-line-graph-lift"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Incidence/LineGraphReconstruction.exists_unique_line_graph_lift"),
            H("The unique lift of the supplied edge isomorphism"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let V and W range over independent universes, and let G and H be simple graphs. "
                    + "Assume that each graph has no three-vertex clique and that each vertex has at least "
                    + "two distinct neighbors. For every supplied isomorphism e between their line graphs, "
                    + "there exists exactly one graph isomorphism f from G to H whose induced line graph "
                    + "isomorphism equals e. Iso denotes graph isomorphisms, and lineGraph denotes the "
                    + "graph construction and its action on isomorphisms. The formula expands unique "
                    + "existence as existence together with equality of every other lift to f.")),
                Paragraph(Text(
                    "Choose two distinct edges incident to a vertex x. Their images intersect at a vertex y. "
                    + "Any third incident edge has an image intersecting both. Restrict these three image "
                    + "edges to their finite endpoint support and apply the intersecting-family "
                    + "classification from DUFStructure. The triangle alternative contradicts the "
                    + "absence of three-vertex cliques. Thus all three images have a common endpoint, "
                    + "which must be y because the first two edges are distinct. This reconstructs "
                    + "the image of the whole incident star at x.")),
                Paragraph(Text(
                    "Apply the same construction to the inverse edge isomorphism. The two original "
                    + "incident edges force the two vertex maps to be inverse. Incidence is then "
                    + "preserved in both directions, so the vertex maps preserve adjacency and the "
                    + "induced unordered edge map is exactly e. Any other lift places the image of x "
                    + "on the same two distinct image edges and therefore agrees at every vertex.")),
                Paragraph(Text(
                    "The vertex types may be empty or infinite, and the graphs may be disconnected. "
                    + "Only the endpoint support used for each local classification is finite. Choice "
                    + "is used inside the proof. The hypotheses are sufficient; no assertion of "
                    + "sharpness or literature priority is made."))),
            DescribeRole.Theorem))));
}
