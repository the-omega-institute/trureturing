using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class LongCoreSignalsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-length zero-block-loss direct-signal obstruction", H("All-length zero-block-loss direct-signal obstruction"),
        Blocks(Paragraph(Text("The source thirty-four-set and complete deletion-failure table are checked in the actual one-cell long-core graph. Folding module labels is an actual neighborhood bijection for every finite module permutation. Triangle-free cover pullback proves minimality of the repeated selection. Exact fiber counts give thirty-four vertices per module, ten selected core vertices per module, and eight in every attached block. Each omitted opposite core root has its unique selected signal port as selected neighbor, while that port has two selected internal neighbors. Thus these actual signals coexist with zero block deficit. This is an obstruction to assigning a positive block loss per signal; it does not refute the solved written thirty-six-per-module upper bound.")),
            Node("baseGraph", "baseGraph", "Exact declaration: def baseGraph : SimpleGraph (Fin 62).", DescribeRole.Definition),
            Node("cover", "cover", "Exact declaration: theorem cover (e : Equiv.Perm I) : CoverPullback.NeighborhoodCover baseGraph.Adj (graph e).Adj Prod.snd.", DescribeRole.Theorem),
            Node("chosen", "chosen", "Exact declaration: def chosen (v : Fin 62) : Prop.", DescribeRole.Definition),
            Node("failure", "failure", "Exact declaration: def failure (v : Fin 62) : Fin 62.", DescribeRole.Definition),
            Node("minimal", "minimal", "Exact declaration: theorem minimal (e : Equiv.Perm I) : Regular.Minimal (graph e).Adj (fun v => chosen v.2).", DescribeRole.Theorem),
            Node("selection", "selection", "Exact declaration: def selection : Finset (I × Fin 62).", DescribeRole.Definition),
            Node("counts", "counts", "Exact declaration: theorem counts : (selection (I.", DescribeRole.Theorem),
            Node("direct_signals", "direct signals", "Exact declaration: theorem direct_signals (e : Equiv.Perm I) (i : I) : (i,(13 : Fin 62))∉selection ∧ (i,(20 : Fin 62))∈selection ∧ (graph e).Adj (i,13) (i,20) ∧ (∀ v, v∈selection → (graph e).Adj (i,13) v → v=(i,20)) ∧ (i,(27 : Fin 62))∈selection ∧ (i,(30 : Fin 62))∈selection ∧ (graph e).Adj (i,20) (i,27) ∧ (graph e).Adj (i,20) (i,30).", DescribeRole.Theorem)), []));
}
