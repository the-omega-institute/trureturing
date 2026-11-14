using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class BinaryCoverRepresentationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/BinaryCoverRepresentation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All actual two-sheeted neighborhood covers are voltage lifts", H("All actual two-sheeted neighborhood covers are voltage lifts"),
        Blocks(Paragraph(Text("Local bijectivity forces the two-by-two incidence matrix above each actual base edge to be a permutation matrix. Explicit two-element fibers provide a labeling and hence an actual graph isomorphism to a binary voltage lift. This representation needs neither connectedness nor a preselected labeling. The fiber condition supplies surjectivity separately from the neighborhood-cover predicate.")),
            Node("adjacency", "adjacency", "Exact declaration: theorem adjacency (c : CoverPullback.NeighborhoodCover G.Adj H.Adj Prod.fst) (v w : V) (a b : F2) : H.Adj (v,a) (w,b) ↔ G.Adj v w ∧ a+b=sign H v w.", DescribeRole.Theorem),
            Node("representation", "representation", "Exact declaration: theorem representation (K : SimpleGraph U) (c : CoverPullback.NeighborhoodCover G.Adj K.Adj p) (h : ∀ v, Fintype.card {u // p u=v}=2) : ∃ s : Voltage G, Nonempty (K ≃g BinaryLift.graph G s).", DescribeRole.Theorem)), []));
}
