using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class CompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/Composition.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local replacement and the exact H0 block cap", H("Local replacement and the exact H0 block cap"),
        Blocks(Paragraph(Text("A minimal ambient selection cannot retain seven vertices in an induced H0 block whose nonport neighborhoods are unchanged. A local dense-selection certificate gives either a safe nonport deletion or an isolated nonport; the latter contradicts formation. The proof replaces an actual local selection and preserves formation throughout the ambient graph. It does not assert the same upper bound for unrestricted attachments.")),
            Node("forms_erase_of_local_replacement", "forms erase of local replacement", "Exact declaration: theorem forms_erase_of_local_replacement {V : Type*} (G : SimpleGraph V) (S tile : Set V) (deleted : V) (hdeleted : deleted ∈ tile) (hforms : Forms G S) (hinside : ∀ x ∈ tile, x ∉ S \\ {deleted} → TwoAt G (S \\ {deleted}) x) (hnooutside : ∀ x, x ∉ tile → ¬ G.Adj x deleted) (hreplace : ∀ center ∈ S, G.Adj center deleted → ∀ x, x ∉ tile → G.Adj x center → ∃ leaf ∈ S \\ {deleted}, G.Adj center leaf) : Forms G (S \\ {deleted}).", DescribeRole.Theorem),
            Node("HasLocalDeletion", "HasLocalDeletion", "Exact declaration: def HasLocalDeletion (selection : Finset (Fin 10)) : Prop.", DescribeRole.Definition),
            Node("HasIsolatedNonport", "HasIsolatedNonport", "Exact declaration: def HasIsolatedNonport (selection : Finset (Fin 10)) : Prop.", DescribeRole.Definition),
            Node("local_dense_certificate", "local dense certificate", "Exact declaration: theorem local_dense_certificate (selection : Finset (Fin 10)) (hcard : 7 ≤ selection.card) : HasIsolatedNonport selection ∨ HasLocalDeletion selection.", DescribeRole.Theorem),
            Node("family_block_upper", "family block upper", "Exact declaration: theorem family_block_upper {I : Type*} (interfaces : I → I → Prop) (S : Set (I × Fin 10)) (hminimal : Minimal (family interfaces) S) (block : I) : (blockSelection S block).card ≤ 6.", DescribeRole.Theorem)), []));
}
