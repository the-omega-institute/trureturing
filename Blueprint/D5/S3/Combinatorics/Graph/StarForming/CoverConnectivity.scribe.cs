using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class CoverConnectivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Connected canonical countercovers and exact triangle scope", H("Connected canonical countercovers and exact triangle scope"),
        Blocks(Paragraph(Text("For a connected simple base graph with a minimal forming selection, a selected vertex lacking a safe certificate has an actual fragile triangle. Exactly one crossed edge in the canonical two-sheeted graph joins its root sheets. Actual base-path lifting and the sheet flip prove connectivity, and the original missing-certificate theorem proves nonminimality of the full pullback. Thus connected two-sheeted tests detect the same failure. The selected pair in the complete triangle has safe self-failures despite violating boundary triangle-freeness. The explicit connected seven-vertex triangle example is minimal but has a connected canonical double cover with nonminimal full pullback. No finite base-order restriction or global surjectivity assumption is introduced.")),
            Node("canonicalGraph", "canonicalGraph", "Exact declaration: def canonicalGraph : SimpleGraph (V × Bool).", DescribeRole.Definition),
            Node("canonical_preconnected", "canonical preconnected", "Exact declaration: theorem canonical_preconnected (hG : G.Preconnected) (hS : Minimal G.Adj S) (hd : S d) (hmissing : ¬ ((¬ TwoAt G.Adj (fun v => S v ∧ v≠d) d) ∨ ∃ outside, SafeFailure G.Adj S d outside)) : (canonicalGraph G S d).Preconnected.", DescribeRole.Theorem),
            Node("connected_countercover", "connected countercover", "Exact declaration: theorem connected_countercover (hG : G.Preconnected) (hS : Minimal G.Adj S) (hd : S d) (hmissing : ¬ ((¬ TwoAt G.Adj (fun v => S v ∧ v≠d) d) ∨ ∃ outside, SafeFailure G.Adj S d outside)) : (canonicalGraph G S d).Preconnected ∧ NeighborhoodCover G.Adj (canonicalGraph G S d).Adj Prod.fst ∧ ¬ Minimal (canonicalGraph G S d).Adj (fun v => S v.1).", DescribeRole.Theorem),
            Node("safe_iff_connected_covers", "safe iff connected covers", "Exact declaration: theorem safe_iff_connected_covers (hG : G.Preconnected) (hS : Minimal G.Adj S) : HasSafeCertificates G.Adj S ↔ ∀ H : SimpleGraph (V × Bool), NeighborhoodCover G.Adj H.Adj Prod.fst → H.Preconnected → Minimal H.Adj (fun v => S v.1).", DescribeRole.Theorem),
            Node("triangle_scope", "triangle scope", "Exact declaration: theorem triangle_scope : let A : Fin 3 → Fin 3 → Prop.", DescribeRole.Theorem),
            Node("sevenNeighbors", "sevenNeighbors", "Exact declaration: def sevenNeighbors (v : Fin 7) : List (Fin 7).", DescribeRole.Definition),
            Node("sevenGraph", "sevenGraph", "Exact declaration: def sevenGraph : SimpleGraph (Fin 7).", DescribeRole.Definition),
            Node("sevenSelected", "sevenSelected", "Exact declaration: def sevenSelected (v : Fin 7) : Prop.", DescribeRole.Definition),
            Node("seven_counterexample", "seven counterexample", "Exact declaration: theorem seven_counterexample : Minimal sevenGraph.Adj sevenSelected ∧ sevenGraph.Preconnected ∧ (canonicalGraph sevenGraph sevenSelected 0).Preconnected ∧ NeighborhoodCover sevenGraph.Adj (canonicalGraph sevenGraph sevenSelected 0).Adj Prod.fst ∧ ¬Minimal (canonicalGraph sevenGraph sevenSelected 0).Adj (fun v => sevenSelected v.1).", DescribeRole.Theorem)), []));
}
