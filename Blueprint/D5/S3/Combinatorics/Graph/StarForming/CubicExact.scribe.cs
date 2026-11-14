using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class CubicExactDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/CubicExact.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrary ambient broken-Heawood block cap", H("Arbitrary ambient broken-Heawood block cap"),
        Blocks(Paragraph(Text("An injective ambient embedding preserves all broken-Heawood edges, and every nonport has exactly its stated internal neighborhood. With those hypotheses, the dense local deletion certificate implies that every ambient inclusion-minimal selection has at most eight vertices in this block. Ports zero and eight remain distinct and may have outside neighbors. No cyclic charge or independent-set formula for an arbitrary interaction graph is inferred here.")),
            Node("lift_broken_star", "lift broken star", "Exact declaration: theorem lift_broken_star {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (embedding : Fin 14 → Vertex) (mask : Fin 16384) (hinjective : ∀ first second, embedding first = embedding second → first = second) (hsound : ∀ first second, BrokenAdj first second → adjacency (embedding first) (embedding second)) (hselection : ∀ vertex, selection (embedding vertex) ↔ chosen mask.val vertex = true) (deleted outside : Fin 14) (hstar : TwoAt BrokenAdj (fun vertex => chosen mask.val vertex = true ∧ vertex ≠ deleted) outside) : TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ embedding deleted) (embedding outside).", DescribeRole.Theorem),
            Node("ambient_heawood_cap", "ambient heawood cap", "Exact declaration: theorem ambient_heawood_cap {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (embedding : Fin 14 → Vertex) (mask : Fin 16384) (hsymmetric : ∀ first second, adjacency first second → adjacency second first) (hinjective : ∀ first second, embedding first = embedding second → first = second) (hsound : ∀ first second, BrokenAdj first second → adjacency (embedding first) (embedding second)) (hselection : ∀ vertex, selection (embedding vertex) ↔ chosen mask.val vertex = true) (hnonport : ∀ vertex, vertex ≠ 0 → vertex ≠ 8 → ∀ outside, adjacency (embedding vertex) outside → ∃ other, outside = embedding other ∧ BrokenAdj vertex other) (hminimal : Minimal adjacency selection) : selectedCard mask.val ≤ 8.", DescribeRole.Theorem)), []));
}
