using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class SubcubicExactDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual ambient ten-vertex core cap", H("The actual ambient ten-vertex core cap"),
        Blocks(Paragraph(Text("The complete 1024-mask dense-core certificate feeds a generic supported-deletion proof in an arbitrary ambient relation. The embedding is injective and induced; only core labels three and eleven may acquire neighbors outside the embedded core. These exact neighborhood hypotheses are preserved. Every minimal selection has at most six core vertices. Actual coverage of the remaining two ports gives SF two exactly eight for the original twelve-vertex graph. Shared-port cyclic identifications, connectivity, exact edge counts and the other invariants of J_r are separate obligations.")),
            Node("supported_deletion", "supported deletion", "Exact declaration: theorem supported_deletion {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (deleted : Vertex) (hforms : Forms adjacency selection) (hnew : TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) deleted) (hadjacent : ∀ outside, ¬ selection outside → adjacency outside deleted → TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) outside) (hreplacement : ∀ center, selection center → adjacency center deleted → ∃ leaf, (selection leaf ∧ leaf ≠ deleted) ∧ adjacency center leaf) : Forms adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted).", DescribeRole.Theorem),
            Node("coreLabel", "coreLabel", "Exact declaration: def coreLabel (vertex : Fin 10) : Fin 12.", DescribeRole.Definition),
            Node("CoreAdj", "CoreAdj", "Exact declaration: def CoreAdj (first second : Fin 10) : Prop.", DescribeRole.Definition),
            Node("attachment", "attachment", "Exact declaration: def attachment (vertex : Fin 10) : Prop.", DescribeRole.Definition),
            Node("coreSelected", "coreSelected", "Exact declaration: def coreSelected (mask : Fin 1024) (vertex : Fin 10) : Prop.", DescribeRole.Definition),
            Node("coreCard", "coreCard", "Exact declaration: def coreCard (mask : Fin 1024) : Nat.", DescribeRole.Definition),
            Node("SafeCore", "SafeCore", "Exact declaration: def SafeCore (mask : Fin 1024) (deleted : Fin 10) : Prop.", DescribeRole.Definition),
            Node("dense_core_certificate", "dense core certificate", "Exact declaration: theorem dense_core_certificate : ∀ mask : Fin 1024, 7 ≤ coreCard mask → ∃ deleted, SafeCore mask deleted.", DescribeRole.Theorem),
            Node("lift_core_star", "lift core star", "Exact declaration: theorem lift_core_star {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (embedding : Fin 10 → Vertex) (mask : Fin 1024) (hinjective : ∀ first second, embedding first = embedding second → first = second) (hedges : ∀ first second, adjacency (embedding first) (embedding second) ↔ CoreAdj first second) (hselection : ∀ vertex, selection (embedding vertex) ↔ coreSelected mask vertex) (deleted outside : Fin 10) (hstar : TwoAt CoreAdj (fun vertex => coreSelected mask vertex ∧ vertex ≠ deleted) outside) : TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ embedding deleted) (embedding outside).", DescribeRole.Theorem),
            Node("ambient_core_cap", "ambient core cap", "Exact declaration: theorem ambient_core_cap {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (embedding : Fin 10 → Vertex) (mask : Fin 1024) (hsymmetric : ∀ first second, adjacency first second → adjacency second first) (hinjective : ∀ first second, embedding first = embedding second → first = second) (hedges : ∀ first second, adjacency (embedding first) (embedding second) ↔ CoreAdj first second) (hselection : ∀ vertex, selection (embedding vertex) ↔ coreSelected mask vertex) (hclosed : ∀ vertex, ¬ attachment vertex → ∀ outside, adjacency (embedding vertex) outside → ∃ other, outside = embedding other) (hminimal : Minimal adjacency selection) : coreCard mask ≤ 6.", DescribeRole.Theorem),
            Node("core_label_properties", "core label properties", "Exact declaration: theorem core_label_properties : Function.Injective coreLabel ∧ (∀ w : Fin 12, w = 0 ∨ w = 6 ∨ ∃ v : Fin 10, coreLabel v = w) ∧ (∀ v : Fin 10, ¬ attachment v → ∀ w : Fin 12, Adj (coreLabel v) w → ∃ other, w = coreLabel other).", DescribeRole.Theorem),
            Node("minimal_card_bound", "minimal card bound", "Exact declaration: theorem minimal_card_bound (S : Finset (Fin 12)) (hS : IsMinimalStarForming graph 2 S) : S.card ≤ 8.", DescribeRole.Theorem),
            Node("sf_graph", "sf graph", "Exact declaration: theorem sf_graph : SF graph 2 = 8.", DescribeRole.Theorem)), []));
}
