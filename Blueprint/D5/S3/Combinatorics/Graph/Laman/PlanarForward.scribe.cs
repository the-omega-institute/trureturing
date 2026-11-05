using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Laman;

internal sealed class PlanarForwardDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Laman/PlanarForward.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/chen2026combinatorialrigidity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite Laman graph has a real planar rigid placement, including the two-vertex case.",
        H("PlanarForward"), Blocks(
            Describe.Lean(DescribeId.Create("planarforward-0"),
                DeclarationHandle.Create(Prefix + "isGenericallyRigid_two"),
                H("From Laman counts to a rigid placement"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every finite vertex type V in any universe and every simple graph G with the Laman property, there exists a real planar placement p whose rigidity kernel has dimension at most three. No construction history is supplied. Strong induction on card(V) maintains the stronger existence of an injective rigid placement. At cardinality two the graph is complete. Above two, the reverse decomposition supplies a degree-two deletion or degree-three deletion with an actual safe bridge edge. The smaller Laman graph is rigid by induction; geometric Type I or Type II preservation and the exact reconstruction isomorphism recover G. Tightness excludes cardinalities zero and one."))), DescribeRole.Theorem)), []));
}
