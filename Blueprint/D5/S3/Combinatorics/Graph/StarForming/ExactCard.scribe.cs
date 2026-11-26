using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class ExactCardDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/ExactCard.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Counting the arbitrary-interface H0 composition", H("Counting the arbitrary-interface H0 composition"),
        Blocks(Paragraph(Text("Each selected vertex belongs to exactly one block. The exact fiber-cardinality sum converts the local six-vertex cap to a global bound and combines it with the displayed minimal selection. Empty index types remain in scope. The canonical SF and beta consequences are proved in Semantics; this module itself concerns actual minimal selections and their cardinalities.")),
            Node("card_eq_sum_blocks", "card eq sum blocks", "Exact declaration: theorem card_eq_sum_blocks {I : Type*} [Fintype I] [DecidableEq I] (S : Finset (I × Fin 10)) : S.card = ∑ block : I, (blockSelection (↑S : Set (I × Fin 10)) block).card.", DescribeRole.Theorem),
            Node("family_card_upper", "family card upper", "Exact declaration: theorem family_card_upper {I : Type*} [Fintype I] [DecidableEq I] (interfaces : I → I → Prop) (S : Finset (I × Fin 10)) (hminimal : Minimal (family interfaces) (↑S : Set (I × Fin 10))) : S.card ≤ 6 * Fintype.card I.", DescribeRole.Theorem),
            Node("exact_composition_card", "exact composition card", "Exact declaration: theorem exact_composition_card {I : Type*} [Fintype I] [DecidableEq I] (interfaces : I → I → Prop) : (∀ S : Finset (I × Fin 10), Minimal (family interfaces) (↑S : Set (I × Fin 10)) → S.card ≤ 6 * Fintype.card I) ∧ (∃ S : Finset (I × Fin 10), Minimal (family interfaces) (↑S : Set (I × Fin 10)) ∧ S.card = 6 * Fintype.card I).", DescribeRole.Theorem)), []));
}
