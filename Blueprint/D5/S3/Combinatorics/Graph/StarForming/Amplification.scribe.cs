using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class AmplificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/Amplification.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local star witnesses and arbitrary H0 interfaces", H("Local star witnesses and arbitrary H0 interfaces"),
        Blocks(Paragraph(Text("The same ten-vertex H0 data is reused from the canonical refutation. Interfaces are arbitrary directed relations on the block indices; no symmetry, connectivity, nonemptiness or distinct-block premise is imposed. Only ports 0 and 5 can acquire external edges. The chosen set is minimal for every interface, has six vertices per block, and admits a proper two-coloring. Cyclic attainment is separate from cyclic connectivity and edge counts.")),
            Node("TwoAt", "TwoAt", "Exact declaration: def TwoAt {V : Type*} (G : SimpleGraph V) (S : Set V) (x : V) : Prop.", DescribeRole.Definition),
            Node("Forms", "Forms", "Exact declaration: def Forms {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop.", DescribeRole.Definition),
            Node("Minimal", "Minimal", "Exact declaration: def Minimal {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop.", DescribeRole.Definition),
            Node("LiteralAt", "LiteralAt", "Exact declaration: def LiteralAt {V : Type*} (G : SimpleGraph V) (S : Set V) (x : V) : Prop.", DescribeRole.Definition),
            Node("literal_iff_local", "literal iff local", "Exact declaration: theorem literal_iff_local {V : Type*} (G : SimpleGraph V) (S : Set V) (x : V) (hx : x ∉ S) : LiteralAt G S x ↔ TwoAt G S x.", DescribeRole.Theorem),
            Node("twoAt_mono", "twoAt mono", "Exact declaration: theorem twoAt_mono {V : Type*} (G : SimpleGraph V) {S T : Set V} (hST : S ⊆ T) {x : V} : TwoAt G S x → TwoAt G T x.", DescribeRole.Theorem),
            Node("minimal_of_deletion_failures", "minimal of deletion failures", "Exact declaration: theorem minimal_of_deletion_failures {V : Type*} (G : SimpleGraph V) (S : Set V) (hforms : Forms G S) (hfail : ∀ selected ∈ S, ∃ x, x ∉ S \\ {selected} ∧ ¬ TwoAt G (S \\ {selected}) x) : Minimal G S.", DescribeRole.Theorem),
            Node("baseEdges", "baseEdges", "Exact declaration: abbrev baseEdges.", DescribeRole.Definition),
            Node("base", "base", "Exact declaration: abbrev base.", DescribeRole.Definition),
            Node("selected", "selected", "Exact declaration: abbrev selected.", DescribeRole.Definition),
            Node("failure", "failure", "Exact declaration: def failure (vertex : Fin 10) : Fin 10.", DescribeRole.Definition),
            Node("Unported", "Unported", "Exact declaration: def Unported (vertex : Fin 10) : Prop.", DescribeRole.Definition),
            Node("family", "family", "Exact declaration: def family {I : Type*} (interfaces : I → I → Prop) : SimpleGraph (I × Fin 10).", DescribeRole.Definition),
            Node("chosen", "chosen", "Exact declaration: def chosen {I : Type*} : Set (I × Fin 10).", DescribeRole.Definition),
            Node("adj_unported", "adj unported", "Exact declaration: theorem adj_unported {I : Type*} (interfaces : I → I → Prop) (first second : I × Fin 10) (hu : Unported first.2) : (family interfaces).Adj first second ↔ first.1 = second.1 ∧ base.Adj first.2 second.2.", DescribeRole.Theorem),
            Node("failure_unported", "failure unported", "Exact declaration: theorem failure_unported (vertex : Fin 10) (hs : vertex ∈ selected) : Unported (failure vertex).", DescribeRole.Theorem),
            Node("base_failure", "base failure", "Exact declaration: theorem base_failure (vertex : Fin 10) (hs : vertex ∈ selected) : failure vertex ∉ selected.erase vertex ∧ (∀ first ∈ selected.erase vertex, ∀ second ∈ selected.erase vertex, base.Adj (failure vertex) first → base.Adj (failure vertex) second → first = second) ∧ (∀ center ∈ selected.erase vertex, base.Adj (failure vertex) center → Unported center ∧ ∀ leaf ∈ selected.erase vertex, ¬ base.Adj center leaf).", DescribeRole.Theorem),
            Node("family_forms", "family forms", "Exact declaration: theorem family_forms {I : Type*} (interfaces : I → I → Prop) : Forms (family interfaces) (chosen : Set (I × Fin 10)).", DescribeRole.Theorem),
            Node("family_deletion_failure", "family deletion failure", "Exact declaration: theorem family_deletion_failure {I : Type*} (interfaces : I → I → Prop) (block : I) (vertex : Fin 10) (hs : vertex ∈ selected) : (block, failure vertex) ∉ (chosen : Set (I × Fin 10)) \\ {(block, vertex)} ∧ ¬ TwoAt (family interfaces) (chosen \\ {(block, vertex)}) (block, failure vertex).", DescribeRole.Theorem),
            Node("family_minimal", "family minimal", "Exact declaration: theorem family_minimal {I : Type*} (interfaces : I → I → Prop) : Minimal (family interfaces) (chosen : Set (I × Fin 10)).", DescribeRole.Theorem),
            Node("chosen_card", "chosen card", "Exact declaration: theorem chosen_card {I : Type*} [Fintype I] [DecidableEq I] : ((Finset.univ : Finset I).product selected).card = 6 * Fintype.card I.", DescribeRole.Theorem),
            Node("family_bipartite", "family bipartite", "Exact declaration: theorem family_bipartite {I : Type*} (interfaces : I → I → Prop) : (family interfaces).Colorable 2.", DescribeRole.Theorem),
            Node("cycleGraph", "cycleGraph", "Exact declaration: def cycleGraph (copies : ℕ) : SimpleGraph (Fin copies × Fin 10).", DescribeRole.Definition),
            Node("cycleSelected", "cycleSelected", "Exact declaration: def cycleSelected (copies : ℕ) : Finset (Fin copies × Fin 10).", DescribeRole.Definition),
            Node("cycle_minimal_card", "cycle minimal card", "Exact declaration: theorem cycle_minimal_card (copies : ℕ) : Minimal (cycleGraph copies) (↑(cycleSelected copies) : Set (Fin copies × Fin 10)) ∧ (cycleSelected copies).card = 6 * copies ∧ (cycleGraph copies).Colorable 2.", DescribeRole.Theorem)), []));
}
