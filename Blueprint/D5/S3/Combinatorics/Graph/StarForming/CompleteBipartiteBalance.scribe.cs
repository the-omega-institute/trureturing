using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class CompleteBipartiteBalanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balanced isolates with positive compensation slack", H("Balanced isolates with positive compensation slack"),
        Blocks(Paragraph(Text("For every d at least two, the actual disjoint union of two complete bipartite graphs Kdd is d-regular bipartite. The two components select opposite whole sides. The selected set is minimal forming and has two d vertices, all isolated, with exactly d on each color side. The actual dissociation maximum is two d, proved for every d by a side-count argument and finite attainment rather than bounded enumeration. Its regular budget is exactly the isolate count two d, but compensation slack is positive two d. This is the received disconnected counterexample to inferring linear equality from balanced isolate-tight accounting. It does not assert connectivity, the converse partition theorem or maximum-exchange classification.")),
            Node("graph", "graph", "Exact declaration: def graph : SimpleGraph (Bool × Fin d).", DescribeRole.Definition),
            Node("part", "part", "Exact declaration: def part (b : Bool) : Finset (Bool × Fin d).", DescribeRole.Definition),
            Node("mem_part", "mem part", "Exact declaration: theorem mem_part (b : Bool) (v : Bool × Fin d) : v ∈ part d b ↔ v.1=b.", DescribeRole.Theorem),
            Node("part_card", "part card", "Exact declaration: theorem part_card (b : Bool) : (part d b).card= d.", DescribeRole.Theorem),
            Node("neighbors", "neighbors", "Exact declaration: theorem neighbors (v : Bool × Fin d) : Finset.univ.filter ((graph d).Adj v) = part d (!v.1).", DescribeRole.Theorem),
            Node("regular", "regular", "Exact declaration: theorem regular (v : Bool × Fin d) : degree (graph d) v= d.", DescribeRole.Theorem),
            Node("part_independent", "part independent", "Exact declaration: theorem part_independent (b : Bool) : IsKIndependent (graph d) 2 (part d b).", DescribeRole.Theorem),
            Node("independent_cap", "independent cap", "Exact declaration: theorem independent_cap (hd : 2 ≤ d) (S : Finset (Bool × Fin d)) (hS : IsKIndependent (graph d) 2 S) : S.card≤d.", DescribeRole.Theorem),
            Node("beta_eq", "beta eq", "Exact declaration: theorem beta_eq (hd : 2 ≤ d) : beta (graph d) 2= d.", DescribeRole.Theorem),
            Node("part_minimal", "part minimal", "Exact declaration: theorem part_minimal (hd : 2 ≤ d) (b : Bool) : IsMinimalStarForming (graph d) 2 (part d b).", DescribeRole.Theorem),
            Node("pairGraph", "pairGraph", "Exact declaration: abbrev pairGraph.", DescribeRole.Definition),
            Node("selection", "selection", "Exact declaration: def selection : Finset ((Bool × Fin d) ⊕ (Bool × Fin d)).", DescribeRole.Definition),
            Node("color", "color", "Exact declaration: def color : ((Bool × Fin d) ⊕ (Bool × Fin d)) → Bool | .inl v => v.1 | .inr v => v.1 theorem pair_coloring : (pairGraph d).Colorable 2.", DescribeRole.Definition),
            Node("pair_coloring", "pair coloring", "Exact declaration: theorem pair_coloring : (pairGraph d).Colorable 2.", DescribeRole.Theorem),
            Node("pair_regular", "pair regular", "Exact declaration: theorem pair_regular (v : (Bool × Fin d) ⊕ (Bool × Fin d)) : degree (pairGraph d) v= d.", DescribeRole.Theorem),
            Node("selection_minimal", "selection minimal", "Exact declaration: theorem selection_minimal (hd : 2 ≤ d) : IsMinimalStarForming (pairGraph d) 2 (selection d).", DescribeRole.Theorem),
            Node("selection_card", "selection card", "Exact declaration: theorem selection_card : (selection d).card=2*d.", DescribeRole.Theorem),
            Node("pair_beta", "pair beta", "Exact declaration: theorem pair_beta (hd : 2 ≤ d) : beta (pairGraph d) 2=2*d.", DescribeRole.Theorem),
            Node("selection_isolates", "selection isolates", "Exact declaration: theorem selection_isolates : isolates (pairGraph d) (selection d)=selection d.", DescribeRole.Theorem),
            Node("color_balance", "color balance", "Exact declaration: theorem color_balance : ((selection d).filter (fun v => color d v=false)).card= d ∧ ((selection d).filter (fun v => color d v=true)).card= d.", DescribeRole.Theorem),
            Node("tight_but_positive", "tight but positive", "Exact declaration: theorem tight_but_positive (hd : 2 ≤ d) : (d:ℤ)*Fintype.card ((Bool × Fin d) ⊕ (Bool × Fin d)) - (2*(d:ℤ)-1)*(selection d).card = (isolates (pairGraph d) (selection d)).card ∧ (d:ℤ)*Fintype.card ((Bool × Fin d) ⊕ (Bool × Fin d)) + 2*(beta (pairGraph d) 2:ℤ) - (2*(d:ℤ)+1)*(selection d).card = 2*(d:ℤ) ∧ 0 < 2*(d:ℤ).", DescribeRole.Theorem)), []));
}
