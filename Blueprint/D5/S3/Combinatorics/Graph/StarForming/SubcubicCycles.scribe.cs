using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class SubcubicCyclesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/SubcubicCycles.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual even cyclic shared-port parameters", H("Actual even cyclic shared-port parameters"),
        Blocks(Paragraph(Text("Alternating cells give the actual bipartition and a displayed perfect matching. The graph has eleven vertices and fourteen edges per cell, five degree-two and six degree-three vertices. For positive even r the actual finite maxima SF, beta, alpha and Gamma have their stated exact values, including r two. This does not assert planarity or the separate cycle-graph theorem.")),
            Node("color", "color", "Exact declaration: def color (phase : I → Bool) (x : I × Fin 11) : Fin 2.", DescribeRole.Definition),
            Node("bipartite", "bipartite", "Exact declaration: theorem bipartite (next : Equiv.Perm I) (phase : I → Bool) (hp : ∀ i, phase (next i)= !(phase i)) : (graph next).Colorable 2.", DescribeRole.Theorem),
            Node("mate", "mate", "Exact declaration: def mate (next : Equiv.Perm I) (phase : I → Bool) (x : I × Fin 11) : I × Fin 11.", DescribeRole.Definition),
            Node("alpha_half", "alpha half", "Exact declaration: theorem alpha_half (next : Equiv.Perm I) (phase : I → Bool) (hp : ∀ i, phase (next i)= !(phase i)) : 2*(graph next).indepNum=11*Fintype.card I.", DescribeRole.Theorem),
            Node("degree_counts", "degree counts", "Exact declaration: theorem degree_counts (next : Equiv.Perm I) : (Finset.univ.filter (fun x => DegreeCapacity.degree (graph next) x=2)).card=5*Fintype.card I ∧ (Finset.univ.filter (fun x => DegreeCapacity.degree (graph next) x=3)).card=6*Fintype.card I.", DescribeRole.Theorem),
            Node("edge_count", "edge count", "Exact declaration: theorem edge_count (next : Equiv.Perm I) : (graph next).edgeFinset.card=14*Fintype.card I.", DescribeRole.Theorem),
            Node("cyclicPhase", "cyclicPhase", "Exact declaration: def cyclicPhase {r : ℕ} (i : Fin r) : Bool.", DescribeRole.Definition),
            Node("cyclic_phase", "cyclic phase", "Exact declaration: theorem cyclic_phase (r : ℕ) (hr : 0<r) (he : Even r) : ∀ i : Fin r, cyclicPhase (finRotate r i)= !(cyclicPhase i).", DescribeRole.Theorem),
            Node("cyclic_parameters", "cyclic parameters", "Exact declaration: theorem cyclic_parameters (r : ℕ) (hr : 0<r) (he : Even r) : let G.", DescribeRole.Theorem)), []));
}
