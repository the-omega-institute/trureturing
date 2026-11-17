using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;

internal sealed class WeightedIndependentBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete include-or-omit checker for weighted independent sets.",
        H("Universal soundness of the complete finite recursion"),
        Blocks(Describe.Lean(DescribeId.Create("weighted-independent-bound-soundness"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/WeightedIndependentBound.sound"),
            H("All compatible subsets"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                "D5/L/QuadraticForms/binarysubspace2026complete")),
            Blocks(Paragraph(Text(
                "For every finite candidate list over any decidable type, every natural weight "
                + "function and every Boolean compatibility relation, the include-or-omit bound "
                + "dominates the weight of every pairwise compatible finite subset. The fuel "
                + "must be at least the full candidate length. In the include branch, erase "
                + "the selected candidate and restrict every other vertex by its compatibility; "
                + "in the omit branch retain the tail. Induction on fuel proves both branches, "
                + "without an assumed maximum, a sample, or a caller-supplied completeness premise. "
                + "The first actual consumer is the received O2 weighted inequality on all63 "
                + "nonzero six-bit vectors, with its complete computed bound19. This independent "
                + "formal checker is a proof representation for the supplied scientific result; "
                + "it does not replace attribution of the manuscript's Gram/radical proof."))),
            DescribeRole.Theorem)), []));
}
