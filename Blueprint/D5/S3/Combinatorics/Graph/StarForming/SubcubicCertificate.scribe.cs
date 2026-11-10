using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class SubcubicCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original subcubic block and forced-certificate collision", H("The original subcubic block and forced-certificate collision"),
        Blocks(Paragraph(Text("The original twelve-vertex graph, ports zero and six, selection of size eight, deletion failures, forced witnesses and simultaneous replacement collision are retained. The complete 4096-mask port-state caps are transported to every actual canonical dissociation subset, giving beta two exactly seven with an attaining port-state witness. The displayed selection is minimal. Both bipartiteness and maximum degree three are checked. The refutation addresses universal subcubic bipartite identification and simultaneous replacement by the two forced certificates. It does not assert the cyclic shared-port family parameters or planarity results.")),
            Node("minimal_of_deletion_failures", "minimal of deletion failures", "Exact declaration: theorem minimal_of_deletion_failures {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (hforms : Forms adjacency selection) (hfail : ∀ deleted, selection deleted → ∃ outside, ¬ (selection outside ∧ outside ≠ deleted) ∧ ¬ TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) outside) : Minimal adjacency selection.", DescribeRole.Theorem),
            Node("neighbors", "neighbors", "Exact declaration: def neighbors (vertex : Fin 12) : List (Fin 12).", DescribeRole.Definition),
            Node("Adj", "Adj", "Exact declaration: def Adj (first second : Fin 12) : Prop.", DescribeRole.Definition),
            Node("selected", "selected", "Exact declaration: def selected (vertex : Fin 12) : Prop.", DescribeRole.Definition),
            Node("failure", "failure", "Exact declaration: def failure (vertex : Fin 12) : Fin 12.", DescribeRole.Definition),
            Node("adjacency_simple", "adjacency simple", "Exact declaration: theorem adjacency_simple : (∀ vertex : Fin 12, ¬ Adj vertex vertex) ∧ (∀ first second : Fin 12, Adj first second ↔ Adj second first).", DescribeRole.Theorem),
            Node("base_forms", "base forms", "Exact declaration: theorem base_forms : Forms Adj selected.", DescribeRole.Theorem),
            Node("base_deletion_failures", "base deletion failures", "Exact declaration: theorem base_deletion_failures : ∀ deleted : Fin 12, selected deleted → ¬ (selected (failure deleted) ∧ failure deleted ≠ deleted) ∧ ¬ TwoAt Adj (fun vertex => selected vertex ∧ vertex ≠ deleted) (failure deleted).", DescribeRole.Theorem),
            Node("base_minimal", "base minimal", "Exact declaration: theorem base_minimal : Minimal Adj selected.", DescribeRole.Theorem),
            Node("forced_certificates", "forced certificates", "Exact declaration: theorem forced_certificates : (∀ outside : Fin 12, ¬ (selected outside ∧ outside ≠ 1) → (¬ TwoAt Adj (fun vertex => selected vertex ∧ vertex ≠ 1) outside ↔ outside = 2)) ∧ (∀ outside : Fin 12, ¬ (selected outside ∧ outside ≠ 7) → (¬ TwoAt Adj (fun vertex => selected vertex ∧ vertex ≠ 7) outside ↔ outside = 10)).", DescribeRole.Theorem),
            Node("selected_card", "selected card", "Exact declaration: theorem selected_card : ((List.finRange 12).filter (fun vertex => decide (selected vertex))).length = 8.", DescribeRole.Theorem),
            Node("membership", "membership", "Exact declaration: def membership (mask : Fin 4096) (vertex : Fin 12) : Bool.", DescribeRole.Definition),
            Node("card", "card", "Exact declaration: def card (mask : Fin 4096) : Nat.", DescribeRole.Definition),
            Node("Dissociation", "Dissociation", "Exact declaration: def Dissociation (mask : Fin 4096) : Prop.", DescribeRole.Definition),
            Node("exchange_collision", "exchange collision", "Exact declaration: theorem exchange_collision : (∀ vertex : Fin 12, membership 1909 vertex = true ↔ (selected vertex ∧ vertex ≠ 1 ∧ vertex ≠ 7) ∨ vertex = 2 ∨ vertex = 10) ∧ card 1909 = 8 ∧ ¬ Dissociation 1909.", DescribeRole.Theorem),
            Node("dissociation_port_cap", "dissociation port cap", "Exact declaration: theorem dissociation_port_cap : ∀ mask : Fin 4096, Dissociation mask → card mask ≤ 6 + if membership mask 0 || membership mask 6 then 1 else 0.", DescribeRole.Theorem),
            Node("portWitness", "portWitness", "Exact declaration: def portWitness (first second : Bool) : Fin 4096.", DescribeRole.Definition),
            Node("port_attainment", "port attainment", "Exact declaration: theorem port_attainment (first second : Bool) : membership (portWitness first second) 0 = first ∧ membership (portWitness first second) 6 = second ∧ Dissociation (portWitness first second) ∧ card (portWitness first second) = 6 + (if first || second then 1 else 0) ∧ (∀ port ∈ ([0,6] : List (Fin 12)), membership (portWitness first second) port = true → ((neighbors port).filter (membership (portWitness first second))).length = 0).", DescribeRole.Theorem),
            Node("graph", "graph", "Exact declaration: def graph : SimpleGraph (Fin 12).", DescribeRole.Definition),
            Node("selectedSet", "selectedSet", "Exact declaration: def selectedSet : Finset (Fin 12).", DescribeRole.Definition),
            Node("maskSet", "maskSet", "Exact declaration: def maskSet (mask : Fin 4096) : Finset (Fin 12).", DescribeRole.Definition),
            Node("mask_dissociation_iff", "mask dissociation iff", "Exact declaration: theorem mask_dissociation_iff (mask : Fin 4096) : Dissociation mask ↔ IsKIndependent graph 2 (maskSet mask).", DescribeRole.Theorem),
            Node("beta_graph", "beta graph", "Exact declaration: theorem beta_graph : beta graph 2 = 7.", DescribeRole.Theorem),
            Node("selectedSet_minimal", "selectedSet minimal", "Exact declaration: theorem selectedSet_minimal : IsMinimalStarForming graph 2 selectedSet.", DescribeRole.Theorem),
            Node("selectedSet_card", "selectedSet card", "Exact declaration: theorem selectedSet_card : selectedSet.card = 8.", DescribeRole.Theorem),
            Node("graph_gap", "graph gap", "Exact declaration: theorem graph_gap : beta graph 2 < SF graph 2.", DescribeRole.Theorem),
            Node("graph_bipartite_subcubic", "graph bipartite subcubic", "Exact declaration: theorem graph_bipartite_subcubic : graph.Colorable 2 ∧ ∀ v, (Finset.univ.filter (graph.Adj v)).card ≤ 3.", DescribeRole.Theorem),
            Node("claim", "claim", "Exact declaration: def claim : Prop.", DescribeRole.Definition),
            Node("result", "result", "Exact declaration: theorem result : ¬ claim.", DescribeRole.Theorem)), []));
}
