using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class H0ParametersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/H0Parameters.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact H0 cyclic degrees and edge counts", H("Exact H0 cyclic degrees and edge counts"),
        Blocks(Paragraph(Text("The unchanged ten-vertex H0 table and actual additional cyclic port edge give exact degrees, edge count seventeen per cell, beta five per cell, SF six per cell and gap one per cell. The cyclic size is at least two, and both degree extrema are attained. The single-block edge restoration and the separate chain structure are not silently included in this edge-count statement.")),
            Node("neighbors", "neighbors", "Exact declaration: def neighbors (e : Equiv.Perm I) (v : I × Fin 10) : List (I × Fin 10).", DescribeRole.Definition),
            Node("degrees", "degrees", "Exact declaration: theorem degrees (e : Equiv.Perm I) (hf : ∀ i,e i≠i) (v : I × Fin 10) : DegreeCapacity.degree (graph e) v= if v.2=2 ∨ v.2=7 then 2 else if v.2=1 ∨ v.2=6 then 3 else 4.", DescribeRole.Theorem),
            Node("edge_count", "edge count", "Exact declaration: theorem edge_count (e : Equiv.Perm I) (hf : ∀ i,e i≠i) : (graph e).edgeFinset.card=17*Fintype.card I.", DescribeRole.Theorem),
            Node("cyclic_parameters", "cyclic parameters", "Exact declaration: theorem cyclic_parameters (r : ℕ) (hr : 2≤r) : let G.", DescribeRole.Theorem)), []));
}
