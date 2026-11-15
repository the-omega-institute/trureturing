using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class HeawoodBareCapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/HeawoodBareCap.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual arbitrary-ambient bare-port Heawood loss", H("Actual arbitrary-ambient bare-port Heawood loss"),
        Blocks(Paragraph(Text("Every selection of the fixed fourteen-vertex broken Heawood block is checked by a complete Boolean certificate. Selections exceeding the exact selected-cardinality plus bare-port budget have an actually safe nonport deletion. The original supported-deletion argument transports this to every actual ambient finite graph with a faithful block embedding and exact nonport neighborhoods. The result counts the two actual bare ports separately and proves cardinality plus bare-port count at most eight. Internal block formation is not assumed. This does not assert the full imported-charge or global block-compensation theorem.")),
            Node("bareBool", "bareBool", "Exact declaration: def bareBool (mask : ℕ) (port : Fin 14) : Bool.", DescribeRole.Definition),
            Node("bareCount", "bareCount", "Exact declaration: def bareCount (mask : ℕ) : ℕ.", DescribeRole.Definition),
            Node("ambient_bare_cap", "ambient bare cap", "Exact declaration: theorem ambient_bare_cap {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (embedding : Fin 14 → Vertex) (mask : Fin 16384) (hsymmetric : ∀ first second, adjacency first second → adjacency second first) (hinjective : ∀ first second, embedding first = embedding second → first = second) (hsound : ∀ first second, BrokenAdj first second → adjacency (embedding first) (embedding second)) (hselection : ∀ vertex, selection (embedding vertex) ↔ chosen mask.val vertex = true) (hnonport : ∀ vertex, vertex ≠ 0 → vertex ≠ 8 → ∀ outside, adjacency (embedding vertex) outside → ∃ other, outside = embedding other ∧ BrokenAdj vertex other) (hminimal : Minimal adjacency selection) : selectedCard mask.val+bareCount mask.val ≤ 8.", DescribeRole.Theorem),
            Node("bareCount_eq", "bareCount eq", "Exact declaration: theorem bareCount_eq (C : Finset (Fin 14)) (mask : Fin 16384) (hmask : ∀ v, chosen mask.val v=true ↔ v ∈ C) : bareCount mask.val=(barePorts C).card.", DescribeRole.Theorem),
            Node("ambient_graph_bare_cap", "ambient graph bare cap", "Exact declaration: theorem ambient_graph_bare_cap {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (embedding : Fin 14 → V) (hinjective : Function.Injective embedding) (hsound : ∀ a b, BrokenAdj a b → G.Adj (embedding a) (embedding b)) (hnonport : ∀ v, v≠0 → v≠8 → ∀ x, G.Adj (embedding v) x → ∃ w, x=embedding w ∧ BrokenAdj v w) (hminimal : StarFormingDissociationRefutation.IsMinimalStarForming G 2 S) : let C.", DescribeRole.Theorem)), []));
}
