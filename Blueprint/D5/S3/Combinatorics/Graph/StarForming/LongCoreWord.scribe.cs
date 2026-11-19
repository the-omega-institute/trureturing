using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class LongCoreWordDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separated long-core words and actual cardinality", H("Separated long-core words and actual cardinality"),
        Blocks(Paragraph(Text("The original two twenty-vertex patterns, internal adjacency table and forward edges are retained unchanged. No consecutive A patterns is an explicit hypothesis. It forces every selected edge to be internal, giving dissociation for arbitrary successor maps. The canonical finite graph selection has size equal to the sum of twelve per A block and ten per B block, and provides that actual beta lower bound. It does not establish all parameters, boundary charges or the full L_k graph identity.")),
            Node("insideRows", "insideRows", "Exact declaration: def insideRows : List (List Nat).", DescribeRole.Definition),
            Node("insideAdj", "insideAdj", "Exact declaration: def insideAdj (first second : Fin 20) : Prop.", DescribeRole.Definition),
            Node("pattern", "pattern", "Exact declaration: def pattern (kind : Bool) : List Nat.", DescribeRole.Definition),
            Node("selected", "selected", "Exact declaration: def selected (kind : Bool) (vertex : Fin 20) : Prop.", DescribeRole.Definition),
            Node("forward", "forward", "Exact declaration: def forward (first second : Fin 20) : Prop.", DescribeRole.Definition),
            Node("wordAdj", "wordAdj", "Exact declaration: def wordAdj {Block : Type} (successor : Block → Block) (first second : Block × Fin 20) : Prop.", DescribeRole.Definition),
            Node("inside_dissociates", "inside dissociates", "Exact declaration: theorem inside_dissociates (kind : Bool) : Dissociates insideAdj (selected kind).", DescribeRole.Theorem),
            Node("pattern_counts", "pattern counts", "Exact declaration: theorem pattern_counts : ∀ kind : Bool, ((List.finRange 20).filter (fun vertex => decide (selected kind vertex))).length = (if kind then 12 else 10) ∧ (([(12, 13), (14, 15), (16, 17)] : List (Nat × Nat)).filter (fun pair => !(pattern kind).contains pair.1 && !(pattern kind).contains pair.2)).length = (if kind then 1 else 2).", DescribeRole.Theorem),
            Node("forward_selected_forces_A", "forward selected forces A", "Exact declaration: theorem forward_selected_forces_A : ∀ firstKind secondKind : Bool, ∀ first second : Fin 20, selected firstKind first → selected secondKind second → forward first second → firstKind = true ∧ secondKind = true.", DescribeRole.Theorem),
            Node("selected_edge_internal", "selected edge internal", "Exact declaration: theorem selected_edge_internal {Block : Type} (successor : Block → Block) (word : Block → Bool) (hseparation : ∀ block, ¬ (word block = true ∧ word (successor block) = true)) (first second : Block × Fin 20) (hfirst : selected (word first.1) first.2) (hsecond : selected (word second.1) second.2) (hedge : wordAdj successor first second) : first.1 = second.1 ∧ insideAdj first.2 second.2.", DescribeRole.Theorem),
            Node("word_dissociates", "word dissociates", "Exact declaration: theorem word_dissociates {Block : Type} (successor : Block → Block) (word : Block → Bool) (hseparation : ∀ block, ¬ (word block = true ∧ word (successor block) = true)) : Dissociates (wordAdj successor) (fun vertex => selected (word vertex.1) vertex.2).", DescribeRole.Theorem),
            Node("inside_simple", "inside simple", "Exact declaration: theorem inside_simple : (∀ v : Fin 20, ¬ insideAdj v v) ∧ (∀ v w : Fin 20, insideAdj v w ↔ insideAdj w v).", DescribeRole.Theorem),
            Node("graph", "graph", "Exact declaration: def graph {Block : Type} (successor : Block → Block) : SimpleGraph (Block × Fin 20).", DescribeRole.Definition),
            Node("selectedSet", "selectedSet", "Exact declaration: def selectedSet (word : Block → Bool) : Finset (Block × Fin 20).", DescribeRole.Definition),
            Node("selectedSet_card", "selectedSet card", "Exact declaration: theorem selectedSet_card (word : Block → Bool) : (selectedSet word).card = ∑ i : Block, (if word i then 12 else 10).", DescribeRole.Theorem),
            Node("beta_word_lower", "beta word lower", "Exact declaration: theorem beta_word_lower (successor : Block → Block) (word : Block → Bool) (hseparation : ∀ block, ¬ (word block = true ∧ word (successor block) = true)) : (∑ i : Block, (if word i then 12 else 10)) ≤ beta (graph successor) 2.", DescribeRole.Theorem)), []));
}
