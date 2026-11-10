using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SubQuorum;

internal sealed class C4FreeRepresentativesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite C4-free representative instances", H("Finite C4-free representative instances"),
        Blocks(Paragraph(Text("The exact Pappus cubic bipartite C4-free graph has beta, psiSq and Omega ten, empty optimal matching and distinct-color dissociation support at ten colors. The actual Heawood parameter distinction and binary-label mixed-support optimum retain their finite scope. The typed Pappus claim/result refutes extending the half-order bound to order eighteen. Positive finite consequences are not certified exempt from utility review.")),
            Node("pappusNeighbors", "pappusNeighbors", "Exact declaration: def pappusNeighbors (vertex : Fin 18) : List Nat.", DescribeRole.Definition),
            Node("pappusSelected", "pappusSelected", "Exact declaration: def pappusSelected : List Nat.", DescribeRole.Definition),
            Node("pappus_regular_bipartite_certificate", "pappus regular bipartite certificate", "Exact declaration: theorem pappus_regular_bipartite_certificate : (∀ vertex : Fin 18, (pappusNeighbors vertex).length = 3 ∧ (pappusNeighbors vertex).Nodup ∧ ∀ neighbor, neighbor ∈ pappusNeighbors vertex → neighbor < 18 ∧ neighbor % 2 ≠ vertex.val % 2) ∧ (∀ first second : Fin 18, second.val ∈ pappusNeighbors first ↔ first.val ∈ pappusNeighbors second).", DescribeRole.Theorem),
            Node("pappus_no_four_cycle_certificate", "pappus no four cycle certificate", "Exact declaration: theorem pappus_no_four_cycle_certificate : ∀ first second : Fin 18, first ≠ second → ((pappusNeighbors first).filter (fun vertex => (pappusNeighbors second).contains vertex)).length ≤ 1.", DescribeRole.Theorem),
            Node("pappus_dissociation_certificate", "pappus dissociation certificate", "Exact declaration: theorem pappus_dissociation_certificate : pappusSelected.length = 10 ∧ pappusSelected.Nodup ∧ (∀ vertex, vertex ∈ pappusSelected → vertex < 18) ∧ (∀ vertex : Fin 18, vertex.val ∈ pappusSelected → ((pappusNeighbors vertex).filter (fun neighbor => pappusSelected.contains neighbor)).length ≤ 1).", DescribeRole.Theorem),
            Node("pappusGraph", "pappusGraph", "Exact declaration: def pappusGraph : SimpleGraph (Fin 18).", DescribeRole.Definition),
            Node("pappusSet", "pappusSet", "Exact declaration: def pappusSet : Finset (Fin 18).", DescribeRole.Definition),
            Node("pappus_class", "pappus class", "Exact declaration: theorem pappus_class : pappusGraph.Colorable 2 ∧ (∀ v, DegreeCapacity.degree pappusGraph v = 3) ∧ NoFourCycle pappusGraph.Adj.", DescribeRole.Theorem),
            Node("pappus_selection", "pappus selection", "Exact declaration: theorem pappus_selection : IsKIndependent pappusGraph 2 pappusSet ∧ pappusSet.card = 10.", DescribeRole.Theorem),
            Node("beta_pappus", "beta pappus", "Exact declaration: theorem beta_pappus : beta pappusGraph 2 = 10.", DescribeRole.Theorem),
            Node("claim", "claim", "Exact declaration: def claim : Prop.", DescribeRole.Definition),
            Node("result", "result", "Exact declaration: theorem result : ¬ claim.", DescribeRole.Theorem),
            Node("heawood_parameters", "heawood parameters", "Exact declaration: theorem heawood_parameters : beta HeawoodParameters.graph 2 = 7 ∧ psiSq HeawoodParameters.graph = 7 ∧ Omega HeawoodParameters.graph = 7 ∧ SF HeawoodParameters.graph 2 = 8.", DescribeRole.Theorem),
            Node("binaryHeawood", "binaryHeawood", "Exact declaration: def binaryHeawood : SimpleGraph (Fin 14).", DescribeRole.Definition),
            Node("mixedSingletons", "mixedSingletons", "Exact declaration: def mixedSingletons : Finset (Fin 14).", DescribeRole.Definition),
            Node("mixedMatching", "mixedMatching", "Exact declaration: def mixedMatching : Finset (Fin 14 × Fin 14).", DescribeRole.Definition),
            Node("mixed_support_optimum", "mixed support optimum", "Exact declaration: theorem mixed_support_optimum : Feasible binaryHeawood mixedSingletons mixedMatching ∧ mixedSingletons.card + mixedMatching.card = Omega binaryHeawood ∧ (mixedSingletons.filter (fun v => heawoodColor v = false)).card = 3 ∧ (mixedSingletons.filter (fun v => heawoodColor v = true)).card = 3.", DescribeRole.Theorem),
            Node("omega_pappus", "omega pappus", "Exact declaration: theorem omega_pappus : Omega pappusGraph = 10.", DescribeRole.Theorem),
            Node("pappus_parameters", "pappus parameters", "Exact declaration: theorem pappus_parameters : beta pappusGraph 2 = 10 ∧ psiSq pappusGraph = 10 ∧ Omega pappusGraph = 10.", DescribeRole.Theorem),
            Node("pappus_optimal_matching_empty", "pappus optimal matching empty", "Exact declaration: theorem pappus_optimal_matching_empty (T : Finset (Fin 18)) (M : Finset (Fin 18 × Fin 18)) (hf : Feasible pappusGraph T M) (hc : T.card + M.card = 10) : M = ∅.", DescribeRole.Theorem),
            Node("pappus_coloring_rigidity", "pappus coloring rigidity", "Exact declaration: theorem pappus_coloring_rigidity (c : Fin 18 → Option ℕ) (hc : IsSubQuorum pappusGraph c) (hp : (palette c Finset.univ).card = 10) : IsKIndependent pappusGraph 2 (coloredSupport c Finset.univ) ∧ (coloredSupport c Finset.univ).card = 10 ∧ Set.InjOn c (coloredSupport c Finset.univ).", DescribeRole.Theorem)), []));
}
