using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class HeawoodInterfacesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Heawood interfaces and loop-aware dissociation optimization", H("Actual Heawood interfaces and loop-aware dissociation optimization"),
        Blocks(Paragraph(Text("The original fourteen-vertex blocks are joined by any simple graph on their two ports. Restored incidences, same-part edges, disconnected and empty finite families are allowed. The original port-omitting minimal eight-set and actual ambient slice cap prove SF=8|I|. The saturated-port theorem forces every dissociation eight-block to be a loop-free independent interaction vertex. Conversely the original eight/seven selections on an attaining loop-aware independent set give actual dissociation attainment, proving beta=7|I|+alpha0. Branching interfaces are counted directly with no cyclic charge reuse. Cyclic and reciprocal connectivity, Gamma/alpha and structural graph properties remain separate obligations.")),
            Node("port", "port", "Exact declaration: def port (p : Fin 2) : Fin 14.", DescribeRole.Definition),
            Node("graph", "graph", "Exact declaration: def graph {I : Type} (P : SimpleGraph (I × Fin 2)) : SimpleGraph (I × Fin 14).", DescribeRole.Definition),
            Node("chosen_minimal", "chosen minimal", "Exact declaration: theorem chosen_minimal (P : SimpleGraph (I × Fin 2)) : IsMinimalStarForming (graph P) 2 chosen.", DescribeRole.Theorem),
            Node("slice_cap", "slice cap", "Exact declaration: theorem slice_cap (P : SimpleGraph (I × Fin 2)) (S : Finset (I × Fin 14)) (hS : IsMinimalStarForming (graph P) 2 S) (i : I) : (slice S i).card ≤ 8.", DescribeRole.Theorem),
            Node("sf_graph", "sf graph", "Exact declaration: theorem sf_graph (P : SimpleGraph (I × Fin 2)) : SF (graph P) 2 = 8 * Fintype.card I.", DescribeRole.Theorem),
            Node("interaction", "interaction", "Exact declaration: def interaction (P : SimpleGraph (I × Fin 2)) (i j : I) : Prop.", DescribeRole.Definition),
            Node("IndependentBlocks", "IndependentBlocks", "Exact declaration: def IndependentBlocks (P : SimpleGraph (I × Fin 2)) (A : Finset I) : Prop.", DescribeRole.Definition),
            Node("beta_graph", "beta graph", "Exact declaration: theorem beta_graph (P : SimpleGraph (I × Fin 2)) : beta (graph P) 2 = 7 * Fintype.card I + alpha0 P.", DescribeRole.Theorem),
            Node("VertexCoverBlocks", "VertexCoverBlocks", "Exact declaration: def VertexCoverBlocks (P : SimpleGraph (I × Fin 2)) (C : Finset I) : Prop.", DescribeRole.Definition),
            Node("alpha0_add_tau0", "alpha0 add tau0", "Exact declaration: theorem alpha0_add_tau0 (P : SimpleGraph (I × Fin 2)) : alpha0 P + tau0 P = Fintype.card I.", DescribeRole.Theorem),
            Node("gap_eq_tau0", "gap eq tau0", "Exact declaration: theorem gap_eq_tau0 (P : SimpleGraph (I × Fin 2)) : SF (graph P) 2 - beta (graph P) 2 = tau0 P.", DescribeRole.Theorem),
            Node("sf_eq_beta_iff", "sf eq beta iff", "Exact declaration: theorem sf_eq_beta_iff (P : SimpleGraph (I × Fin 2)) : SF (graph P) 2 = beta (graph P) 2 ↔ P = ⊥.", DescribeRole.Theorem),
            Node("bipartite", "bipartite", "Exact declaration: theorem bipartite (P : SimpleGraph (I × Fin 2)) (hP : ∀ i j p q, P.Adj (i,p) (j,q) → p ≠ q) : (graph P).Colorable 2.", DescribeRole.Theorem)), []));
}
