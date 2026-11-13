using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class CazenaveLaplacianRankBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/CazenaveLaplacianRankBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/cazenave2026spectralgraphconjectures");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The second largest ordinary Laplacian eigenvalue plus real adjacency rank is at most twice the edge count.",
        H("Cazenave's Laplacian–rank inequality"),
        Blocks(
            Node("claim", "Conjecture 5 (#239534)",
                new Formula.Relation(Call("claim"), FormulaRelationOperator.Equal,
                    Seq(Open, ClaimBody(), Close)),
                "Conjecture 5 of Lemmas and Conjectures in Spectral Graph Theory states that the second largest ordinary Laplacian eigenvalue plus adjacency rank is at most twice the number of edges. Section 1 fixes simple undirected connected graphs of order at least two, L = D − A and decreasing eigenvalues counted with multiplicity. Fin (n + 2) ranges over every permitted order. The adjacency matrix and its rank are over Real. The edgeFinset cardinality counts each unordered edge once. Decidable adjacency supplies instance data for the same graph.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The unrestricted Laplacian–rank bound", ClaimBody(),
                "Positivity and decreasing order give twice the second eigenvalue at most the Laplacian trace, which is twice the edge count. Adjacency rank is at most graph order. These estimates settle graphs with at least as many edges as vertices, and the sparse branch when rank is below full rank. A remaining connected graph has one fewer edge than vertices and is a tree. At order two the smaller Laplacian eigenvalue is zero. At larger order, full adjacency rank forces an internal edge: otherwise two degree-one neighbours of a vertex of degree at least two have identical adjacency rows. Deleting an internal bridge partitions the vertices into two sides, each of size at least two. On the hyperplane where the endpoint coordinates agree, the bridge energy vanishes. Complete-side energy bounds give a Rayleigh upper bound equal to graph order minus two. A nonzero vector in the top-two spectral plane meets this hyperplane, and its Rayleigh lower bound gives the required second-eigenvalue estimate. All inequalities concern the same graph, vector and ordinary real Laplacian.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("op-cazenave2611c5"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("cazenave-laplacian-rank-" + name),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Op(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Op(name) : new Formula.Apply(Op(name), [.. args]);
    private static Formula App(Formula value, params Formula[] args) =>
        new Formula.Apply(value, [.. args]);
    private static Formula DotName(Formula value, string name) =>
        Seq(Open, value, Close, Dot, Op(name));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula RealCast(Formula value) => Seq(Open, value, Sp, Colon, Sp, C("Real"), Close);

    private static Formula ClaimBody()
    {
        Formula size = Seq(V("n"), Plus, D(2));
        Formula lap = new Formula.Apply(
            Seq(Op("LinWangCaiBroomSpectralRatio"), Dot, Op("lapEig")), [V("G"), D(1)]);
        Formula rank = RealCast(DotName(App(DotName(V("G"), "adjMatrix"), C("Real")), "rank"));
        Formula edges = RealCast(DotName(DotName(V("G"), "edgeFinset"), "card"));
        Formula inequality = new Formula.Relation(
            Seq(lap, Plus, rank), FormulaRelationOperator.LessThanOrEqual,
            Seq(D(2), Sp, Cdot, Sp, edges));
        return All("n", C("Nat"),
            All("G", Call("SimpleGraph", Call("Fin", size)),
                Seq(OpenBracket, Call("DecidableRel", DotName(V("G"), "Adj")),
                    CloseBracket, Sp, new Formula.Logic(
                        DotName(V("G"), "Connected"), FormulaLogicOperator.Implies, inequality))));
    }
}
