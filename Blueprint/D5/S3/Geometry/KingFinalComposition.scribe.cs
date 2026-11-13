using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KingFinalCompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KingFinalComposition.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/carnerobravo2025independenceproducts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral torsion in an induced king-grid graph", H("Integral torsion in an induced king-grid graph"), Blocks(
            Node("n0", "replayToRouteBaseIso", "The same finite endpoint",
                "Literal natural labels and adjacency identify the forty-move endpoint with the base graph of the 178 prescribed routes."),
            Node("n1", "selectedReducedHomologyIso", "The total suspension transport",
                "The forty moves and 31286 prescribed triple subdivisions give an isomorphism from the selected independence realization in reduced degree q+31326 to the actual seed realization in degree q, for q at least one."),
            Node("n2", "selectedSingularHomologyIso", "Ordinary integral degree 31327",
                "The actual singular seed comparison and positive-degree reduced-to-ordinary isomorphisms identify ordinary integral singular homology in degree 31327 of the selected realization with ordinary integral H1 of the seed realization."),
            Node("n3", "selectedSingularClass_nonzero_killed_by_two", "A nonzero class killed by two",
                "The original seed cycle transports to a nonzero class of ordinary integral singular homology in degree 31327 of the actual selected induced graph. Twice this class is zero."),
            Node("n4", "selected_not_sourceSP", "The sphere-bouquet obstruction",
                "The selected finite realization is compact. The compact sourceSP torsion theorem, with arbitrary sphere indexing families, dimensions including zero and arbitrary basepoints in the ordinary quotient wedge topology, contradicts its nonzero positive-degree integral torsion."),
            Node("n5", "rectangle_not_sourceSW", "The hereditary counterexample",
                "The selected set is nonempty, so its failure of sourceSP refutes sourceSW for the strong product of paths on 9337 and 9061 vertices. The formal sourceSW convention excludes empty induced sets; the source paper leaves its vertexless convention unspecified. This nonempty obstruction is independent of that convention."),
            Node("n7", "result", "The universal hereditary extension is false",
                "The claim quantifies over every pair of positive path orders and every nonempty induced set, with the original sourceSP alternatives. The actual selected nonempty graph refutes that universal statement. The claim and result retain their arbitrary sphere-index universe parameter. The utility header separately enrolls their closed universe-zero instance as utilityClaim and utilityRefutation; that administrative enrollment adds no mathematical contribution and does not establish the full arbitrary-family scope, which is supplied by the unchanged polymorphic result."),
            Node("n6", "question32_counterexample", "Question 32",
                "The actual selected induced graph has 93999 vertices and 94036 edges and fails sourceSP. It gives the hereditary obstruction asked in Question 32 of Carnero Bravo. Question 35 concerns the entire rectangle and has a different conclusion. The seed and suspension mechanisms retain their classical attribution; no priority or exhaustive later-literature claim follows from these mathematical statements."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose, DescribeRole? role = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
