using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Triameter.TriameterNotation;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Triameter;

internal sealed class CliqueChainsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/Triameter/CliqueChains";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/hakkozerenko2026triameter");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The equality cases of the triameter bound by independence are three chains of split cliques.",
        H("Triameter and chains of split cliques"),
        Blocks(
            Paragraph(Text("Let G be a simple undirected graph on a finite vertex type V. "
                + "The distance between vertices of a connected G is the minimum number of edges in a walk "
                + "between them. The triameter tr(G) is the maximum of d(x,y)+d(x,z)+d(y,z) over all ordered "
                + "triples of vertices, with repeats allowed. The independence number α(G) is the "
                + "largest size of an independent set.")),
            Definition("clique-chain-block-index", "BlockIndex",
                Eqn(Call("BlockIndex", Id("q")), Call("Option", LayerIndices(i => Call("q", i)))),
                "For q : Fin 3 → ℕ, none indexes the central clique. A pair of leg i and index in Fin (q i) "
                    + "indexes a peripheral clique on that leg."),
            Definition("clique-chain-block", "block",
                Eqn(Block(Id("x")), Seq(Qualified("if"), Sp, Eqn(Depth(Id("x")), D(0)),
                    Sp, Qualified("then"), Sp, Qualified("none"), Sp, Qualified("else"), Sp,
                    Call("some", Seq(Langle, Leg(Id("x")), Comma, Sp,
                        Call("Nat.div", Seq(Depth(Id("x")), Minus, D(1)), D(2)),
                        Rangle)))),
                "For x : EvenLegTriangle.Vertex q, block x returns a BlockIndex q. At positive depth, "
                    + "natural division by two after subtracting one gives the index in Fin (q i)."),
            Definition("clique-chain-interface", "Interface",
                Seq(Call("Interface", Id("x"), Id("y")), Sp, Leftrightarrow, Sp,
                    SameLeg, Sp, Land, Sp, Parenthesized(Seq(
                        Parenthesized(OrientedInterface(Id("x"), Id("y"))), Sp, Lor, Sp,
                        Parenthesized(OrientedInterface(Id("y"), Id("x")))))),
                "For x y : EvenLegTriangle.Vertex q, an interface links consecutive depths on the same leg "
                    + "whose smaller depth is even. The two cases give the two orientations."),
            Definition("clique-chain-construction", "CliqueChains",
                Seq(Chains, Sp, Leftrightarrow, Sp, Surjective, Nl, Sp, Land, Sp,
                    Parenthesized(Seq(Forall, Sp, Id("x"), Sp, Id("y"), Comma, Sp,
                        Id("x"), Neq, Id("y"), Sp, Longrightarrow, Sp, SameBlock,
                        Sp, Longrightarrow, Sp, GraphAdj)), Nl, Sp, Land, Sp,
                    Parenthesized(Seq(Forall, Sp, Id("x"), Sp, Id("y"), Comma, Sp,
                        GraphAdj, Sp, Longrightarrow, Sp, SameBlock, Sp, Lor, Sp,
                        Call("Interface", Image(Id("x")), Image(Id("y"))))), Nl, Sp, Land, Sp,
                    Parenthesized(EdgeLift(Call("Interface", Id("u"), Id("v"))))),
                "For G : SimpleGraph V, q : Fin 3 → ℕ and f : V → EvenLegTriangle.Vertex q, the four clauses "
                    + "are layers_nonempty, within_cliques, allowed_edges and interfaces_nonempty. "
                    + "The last clause requires one edge over each ordered interface."),
            Describe.Lean(
                DescribeId.Create("triameter-independence-equality"),
                DeclarationHandle.Create(Owner + ".question1"),
                H("Hak–Kozerenko Question 1 at k = 1"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Question 1. Theorem 1.1 determines the distances between the vertices of a "
                        + "triametral triple in graphs attaining the equality in (1), but not the whole graph. "
                        + "Characterize the graphs attaining this equality, at least for k = 1, that is, "
                        + "the graphs G with tr(G) = 4α(G) − 1.")),
                    Paragraph(Text("The source assumes at least three vertices. The equivalence uses only "
                        + "finiteness and connectedness and also holds on connected vertex sets of size one "
                        + "or two. Fin(3) indexes the three chains. For each chain i the nonnegative length "
                        + "is q(i), and EvenLegTriangle.Vertex q is the disjoint union over i of depths 0 through 2q(i). "
                        + "A surjection f from V to EvenLegTriangle.Vertex q partitions V into nonempty layers. "
                        + "The three depth-zero layers form the central clique. For each 1 ≤ t ≤ q(i), "
                        + "depths 2t−1 and 2t are the inward and outward layers of clique t on chain i.")),
                    Paragraph(Text("CliqueChains requires every pair of distinct vertices in the same clique "
                        + "to be adjacent. Every edge between different cliques joins depth 2t to depth 2t+1 "
                        + "on the same chain i, for 0 ≤ t < q(i). Each such interface has an arbitrary "
                        + "nonempty edge set. At t = 0 the interface starts at the depth-zero layer of chain i "
                        + "in the central clique. A chain of length zero has no interface. The within-clique "
                        + "and interface edges exhaust the graph's edges.")),
                    Paragraph(Text("A maximizing triple projects onto three legs with a common point or "
                        + "a triangular centre. Equality in the distance-packing bound forces a triangular "
                        + "centre and even legs. For each central or peripheral block one can choose an "
                        + "independent set of model vertices away from the block. Lifting this set shows that "
                        + "a missing edge within a block would exceed the independence number. The projection "
                        + "also lifts each interface edge. Conversely, each clique contributes at most one "
                        + "vertex to an independent set, and vertices at the ends of the three chains certify "
                        + "the required lower bound on triameter. The general bound then forces equality."))),
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock.Describe Definition(string id, string name, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + "." + name), H(name),
            StatementSource.FromAuthor(F.Disp(statement)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Chains => Call("CliqueChains", Id("G"), Id("q"), Id("f"));
    private static Formula Block(Formula x) => Call("block", x);
    private static Formula SameBlock => Eqn(Block(Image(Id("x"))), Block(Image(Id("y"))));
    private static Formula OrientedInterface(Formula x, Formula y) =>
        Seq(Eqn(Call("Nat.mod", Depth(x), D(2)), D(0)), Sp, Land, Sp, Step(x, y));

    private static Formula Statement() =>
        GraphForall(Seq(Connected, Sp, Longrightarrow, Sp, Parenthesized(Seq(
            Equality, Sp, Leftrightarrow, Sp, Exists, Sp, LegAndMapBinders, Comma, Sp, Chains))));
}
