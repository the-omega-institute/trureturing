using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class HeawoodParametersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact canonical Heawood invariants", H("Exact canonical Heawood invariants"),
        Blocks(Paragraph(Text("The original Fano graph and supplier minimal eight-set are reused. The exact finite dissociation cap ranges over every subset of this fixed fourteen-vertex graph, and an actual bipartition side attains seven. The general degree-capacity theorem bounds every minimal selection by eight. Thus beta two is seven and SF two is eight for this cubic bipartite graph, refuting the universal cubic bipartite identification. This does not prove the all-r interface, cover or graph-structure assertions.")),
            Node("fanoNeighbors", "fanoNeighbors", "Exact declaration: def fanoNeighbors (vertex : Fin 14) : List (Fin 14).", DescribeRole.Definition),
            Node("FanoAdj", "FanoAdj", "Exact declaration: def FanoAdj (first second : Fin 14) : Prop.", DescribeRole.Definition),
            Node("fanoSelected", "fanoSelected", "Exact declaration: def fanoSelected (vertex : Fin 14) : Prop.", DescribeRole.Definition),
            Node("fanoFailure", "fanoFailure", "Exact declaration: def fanoFailure (vertex : Fin 14) : Fin 14.", DescribeRole.Definition),
            Node("fano_simple_cubic", "fano simple cubic", "Exact declaration: theorem fano_simple_cubic : (∀ vertex : Fin 14, ¬ FanoAdj vertex vertex) ∧ (∀ first second : Fin 14, FanoAdj first second ↔ FanoAdj second first) ∧ (∀ vertex : Fin 14, (fanoNeighbors vertex).length = 3 ∧ (fanoNeighbors vertex).Nodup).", DescribeRole.Theorem),
            Node("fano_forms", "fano forms", "Exact declaration: theorem fano_forms : Forms FanoAdj fanoSelected.", DescribeRole.Theorem),
            Node("fano_deletion_failures", "fano deletion failures", "Exact declaration: theorem fano_deletion_failures : ∀ deleted : Fin 14, fanoSelected deleted → ¬ (fanoSelected (fanoFailure deleted) ∧ fanoFailure deleted ≠ deleted) ∧ ¬ TwoAt FanoAdj (fun vertex => fanoSelected vertex ∧ vertex ≠ deleted) (fanoFailure deleted).", DescribeRole.Theorem),
            Node("fano_minimal", "fano minimal", "Exact declaration: theorem fano_minimal : Minimal FanoAdj fanoSelected.", DescribeRole.Theorem),
            Node("fano_selected_card", "fano selected card", "Exact declaration: theorem fano_selected_card : ((List.finRange 14).filter (fun vertex => decide (fanoSelected vertex))).length = 8.", DescribeRole.Theorem),
            Node("graph", "graph", "Exact declaration: def graph : SimpleGraph (Fin 14).", DescribeRole.Definition),
            Node("selectedSet", "selectedSet", "Exact declaration: def selectedSet : Finset (Fin 14).", DescribeRole.Definition),
            Node("maskSet", "maskSet", "Exact declaration: def maskSet (mask : Fin 16384) : Finset (Fin 14).", DescribeRole.Definition),
            Node("maskDissociates", "maskDissociates", "Exact declaration: def maskDissociates (mask : Fin 16384) : Prop.", DescribeRole.Definition),
            Node("mask_dissociation_iff", "mask dissociation iff", "Exact declaration: theorem mask_dissociation_iff (mask : Fin 16384) : maskDissociates mask ↔ IsKIndependent graph 2 (maskSet mask).", DescribeRole.Theorem),
            Node("mask_cap", "mask cap", "Exact declaration: theorem mask_cap (mask : Fin 16384) (h : maskDissociates mask) : ((List.finRange 14).filter (fun v => mask.val.testBit v.val)).length ≤ 7.", DescribeRole.Theorem),
            Node("beta_graph", "beta graph", "Exact declaration: theorem beta_graph : beta graph 2 = 7.", DescribeRole.Theorem),
            Node("sf_graph", "sf graph", "Exact declaration: theorem sf_graph : SF graph 2 = 8.", DescribeRole.Theorem),
            Node("graph_class", "graph class", "Exact declaration: theorem graph_class : graph.Colorable 2 ∧ ∀ v, (Finset.univ.filter (graph.Adj v)).card = 3.", DescribeRole.Theorem),
            Node("claim", "claim", "Exact declaration: def claim : Prop.", DescribeRole.Definition),
            Node("result", "result", "Exact declaration: theorem result : ¬ claim.", DescribeRole.Theorem)), []));
}
