using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class BipartiteExchangeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange.";
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual augmented bipartite exchanges", H("Actual augmented bipartite exchanges"),
        Blocks(Paragraph(Text("For every actual minimal two-star-forming selection in a finite bipartite graph, chosen high witnesses and additional unreserved-leaf witnesses form one injective outside map. The two explicit exchange selections are canonical dissociation sets. Their cardinalities plus the actual selected isolate count equal twice the selected size. Consequently 2|S|<=2 beta plus selected isolates, without a regularity, connectivity or nonempty assumption. Empty high/leaf classes and disconnected graphs remain in scope.")),
            Node("Isolate", "Isolate", "Exact declaration: def Isolate (v : V) : Prop.", DescribeRole.Definition),
            Node("LeafAt", "LeafAt", "Exact declaration: def LeafAt (u h : V) : Prop.", DescribeRole.Definition),
            Node("witness_failure", "witness failure", "Exact declaration: theorem witness_failure (hS : IsMinimalStarForming G 2 S) (v : V) (hv : High G.Adj (· ∈ S) v) : Failure G.Adj (· ∈ S) v (witness G S hS v).", DescribeRole.Theorem),
            Node("witness_injective", "witness injective", "Exact declaration: theorem witness_injective (hS : IsMinimalStarForming G 2 S) (v w : V) (hv : High G.Adj (· ∈ S) v) (hw : High G.Adj (· ∈ S) w) (he : witness G S hS v = witness G S hS w) : v = w.", DescribeRole.Theorem),
            Node("adjacent_other_isolate", "adjacent other isolate", "Exact declaration: theorem adjacent_other_isolate (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (h x y : V) (hf : Failure G.Adj (· ∈ S) h x) (hxh : G.Adj x h) (hy : y ∈ S) (hne : y ≠ h) (hxy : G.Adj x y) : Isolate G S y.", DescribeRole.Theorem),
            Node("nonadjacent_leaf", "nonadjacent leaf", "Exact declaration: theorem nonadjacent_leaf (hS : IsMinimalStarForming G 2 S) (h x : V) (hh : High G.Adj (· ∈ S) h) (hf : Failure G.Adj (· ∈ S) h x) (hne : ¬ G.Adj x h) : ∃ u, LeafAt G S u h ∧ G.Adj x u ∧ ∀ w ∈ S, G.Adj x w → w = u.", DescribeRole.Theorem),
            Node("leaf_support_unique", "leaf support unique", "Exact declaration: theorem leaf_support_unique (u h k : V) (hh : LeafAt G S u h) (hk : LeafAt G S u k) : h = k.", DescribeRole.Theorem),
            Node("nonhigh_unique", "nonhigh unique", "Exact declaration: theorem nonhigh_unique (v x y : V) (hv : v ∈ S) (hn : ¬ High G.Adj (· ∈ S) v) (hx : x ∈ S) (hy : y ∈ S) (hax : G.Adj v x) (hay : G.Adj v y) : x = y.", DescribeRole.Theorem),
            Node("Reserved", "Reserved", "Exact declaration: def Reserved (hS : IsMinimalStarForming G 2 S) (u : V) : Prop.", DescribeRole.Definition),
            Node("Extra", "Extra", "Exact declaration: def Extra (hS : IsMinimalStarForming G 2 S) (u : V) : Prop.", DescribeRole.Definition),
            Node("Active", "Active", "Exact declaration: def Active (hS : IsMinimalStarForming G 2 S) (u : V) : Prop.", DescribeRole.Definition),
            Node("Passive", "Passive", "Exact declaration: def Passive (hS : IsMinimalStarForming G 2 S) (u : V) : Prop.", DescribeRole.Definition),
            Node("leaf_not_high", "leaf not high", "Exact declaration: theorem leaf_not_high (u h : V) (hu : LeafAt G S u h) : ¬ High G.Adj (· ∈ S) u.", DescribeRole.Theorem),
            Node("reserved_leaf", "reserved leaf", "Exact declaration: theorem reserved_leaf (hS : IsMinimalStarForming G 2 S) (u : V) (hu : Reserved G S hS u) : ∃ h, LeafAt G S u h ∧ ¬ G.Adj (witness G S hS h) h ∧ G.Adj (witness G S hS h) u.", DescribeRole.Theorem),
            Node("extra_has_failure", "extra has failure", "Exact declaration: theorem extra_has_failure (hS : IsMinimalStarForming G 2 S) (u : V) (hu : Extra G S hS u) : ∃ x, Failure G.Adj (· ∈ S) u x ∧ G.Adj x u.", DescribeRole.Theorem),
            Node("active_failure", "active failure", "Exact declaration: theorem active_failure (hS : IsMinimalStarForming G 2 S) (u : V) (hu : Active G S hS u) : Failure G.Adj (· ∈ S) u (activeWitness G S hS u).", DescribeRole.Theorem),
            Node("active_selected", "active selected", "Exact declaration: theorem active_selected (hS : IsMinimalStarForming G 2 S) (u : V) (hu : Active G S hS u) : u ∈ S.", DescribeRole.Theorem),
            Node("active_not_isolate", "active not isolate", "Exact declaration: theorem active_not_isolate (hS : IsMinimalStarForming G 2 S) (u : V) (hu : Active G S hS u) : ¬ Isolate G S u.", DescribeRole.Theorem),
            Node("extra_witness_adjacent", "extra witness adjacent", "Exact declaration: theorem extra_witness_adjacent (hS : IsMinimalStarForming G 2 S) (u : V) (hu : Extra G S hS u) : G.Adj (activeWitness G S hS u) u.", DescribeRole.Theorem),
            Node("reserved_passive", "reserved passive", "Exact declaration: theorem reserved_passive (hS : IsMinimalStarForming G 2 S) (u : V) (hu : Reserved G S hS u) : Passive G S hS u.", DescribeRole.Theorem),
            Node("active_shape", "active shape", "Exact declaration: theorem active_shape (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hS : IsMinimalStarForming G 2 S) (a v : V) (ha : Active G S hS a) (hv : v ∈ S) (hxv : G.Adj (activeWitness G S hS a) v) : Isolate G S v ∨ v = a ∨ (Passive G S hS v ∧ G.Adj a v).", DescribeRole.Theorem),
            Node("activeWitness_injective", "activeWitness injective", "Exact declaration: theorem activeWitness_injective (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hS : IsMinimalStarForming G 2 S) (a b : V) (ha : Active G S hS a) (hb : Active G S hS b) (heq : activeWitness G S hS a = activeWitness G S hS b) : a = b.", DescribeRole.Theorem),
            Node("active_passive_edges", "active passive edges", "Exact declaration: theorem active_passive_edges (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hS : IsMinimalStarForming G 2 S) (a b : V) (ha : Active G S hS a) (hb : Passive G S hS b) : G.Adj a b ↔ G.Adj (activeWitness G S hS a) b.", DescribeRole.Theorem),
            Node("active_passive_unique", "active passive unique", "Exact declaration: theorem active_passive_unique (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hS : IsMinimalStarForming G 2 S) (a b c : V) (ha : Active G S hS a) (hb : Passive G S hS b) (hc : Passive G S hS c) (hab : G.Adj a b) (hac : G.Adj a c) : b = c.", DescribeRole.Theorem),
            Node("exchange_dissociation", "exchange dissociation", "Exact declaration: theorem exchange_dissociation (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hS : IsMinimalStarForming G 2 S) (c : Bool) : IsKIndependent G 2 (exchange G S hS color c).", DescribeRole.Theorem),
            Node("exchange_card_sum", "exchange card sum", "Exact declaration: theorem exchange_card_sum (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hS : IsMinimalStarForming G 2 S) : (exchange G S hS color false).card + (exchange G S hS color true).card + (DegreeCapacity.isolates G S).card = 2 * S.card.", DescribeRole.Theorem),
            Node("selection_compensation", "selection compensation", "Exact declaration: theorem selection_compensation (hG : G.Colorable 2) (S : Finset V) (hS : IsMinimalStarForming G 2 S) : 2 * S.card ≤ 2 * beta G 2 + (DegreeCapacity.isolates G S).card.", DescribeRole.Theorem)), []));
}
