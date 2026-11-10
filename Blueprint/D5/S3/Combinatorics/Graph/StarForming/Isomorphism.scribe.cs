using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class IsomorphismDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/Isomorphism.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Graph isomorphisms preserve actual finite maxima", H("Graph isomorphisms preserve actual finite maxima"),
        Blocks(Paragraph(Text("Actual selected images transport formation, inclusion-minimality and dissociation in both directions. The finite maxima beta and SF are invariant, with actual attaining images. Empty finite types are included.")),
            Node("minimal_image_iff", "minimal image iff", "Exact declaration: theorem minimal_image_iff (e : G ≃g H) (S : Finset V) : IsMinimalStarForming H 2 (S.image e) ↔ IsMinimalStarForming G 2 S.", DescribeRole.Theorem),
            Node("independent_image_iff", "independent image iff", "Exact declaration: theorem independent_image_iff (e : G ≃g H) (S : Finset V) : IsKIndependent H 2 (S.image e) ↔ IsKIndependent G 2 S.", DescribeRole.Theorem),
            Node("parameters", "parameters", "Exact declaration: theorem parameters (e : G ≃g H) : beta G 2 = beta H 2 ∧ SF G 2 = SF H 2.", DescribeRole.Theorem)), []));
}
