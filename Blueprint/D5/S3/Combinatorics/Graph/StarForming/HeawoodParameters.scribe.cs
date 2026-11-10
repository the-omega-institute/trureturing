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
