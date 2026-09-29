using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowWilfFixedInsertionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowWilfFixedInsertion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical insertion makes a chosen new value a singleton cycle in the inverse Foata map.",
        H("Insertion and Singleton Cycles"),
        Blocks(
            Node("fixed-insert", "Canonical singleton insertion", "fixedInsert", "The recursive insertion places a new value f immediately before the first value at least f, or at the end if none exists; it preserves the order of the old entries.", DescribeRole.Definition),
            Node("fixed-insert-permutation", "Insertion preserves the old word", "fixedInsert_perm", "The inserted word is a permutation of f followed by the original word.", DescribeRole.Theorem),
            Node("erase-fixed-insert", "Erasing the inserted point", "erase_fixedInsert", "When f is absent from p, erasing f from fixedInsert f p returns p.", DescribeRole.Theorem),
            Node("insert-commutation", "Commutation of distinct insertions", "fixedInsert_comm", "For distinct new values f and g absent from p, inserting f and g in either order gives the same word.", DescribeRole.Theorem),
            Node("fixed-insert-inverse", "Fixed points are exactly canonical insertions", "fixedInsert_erase_eq_iff_hat_fixed", "For a word with distinct entries containing f, reinserting f after erasure recovers the word exactly when hat fixes f.", DescribeRole.Theorem),
            Node("fixed-syntax", "Singleton-block syntax", "FixedSyntax", "FixedSyntax f p records the recursive word shape in which f begins a singleton block: entries before f are smaller and the next entry, when present, is larger.", DescribeRole.Definition),
            Node("fixed-syntax-characterization", "Syntax and fixed points", "fixedSyntax_iff_hat_fixed", "For a word with distinct entries containing f, FixedSyntax f p is equivalent to hat p f equal to f.", DescribeRole.Theorem),
            Node("fixed-insert-preservation", "Other fixed points under insertion", "hat_fixed_fixedInsert_iff", "If f is freshly inserted, the fixed-point status of any distinct old value g is unchanged.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
