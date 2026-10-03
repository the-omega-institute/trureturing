using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class CoupledOrderedRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/CoupledOrderedRecovery.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/koprowski2026enumeration");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Increasing slot order transports low-subword deletion and reads a replacement permutation exactly.",
        H("Ordered low-subword recovery"),
        Blocks(
            Describe.Lean(DescribeId.Create("shared-ordered-recovery"),
                DeclarationHandle.Create(Prefix + "shared_ordered_recovery"),
                H("Deletion and replacement in increasing low-slot order"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Consider families cut, slotOrder, lowWord and replace on finite permutations. At every size n and threshold T at most n, slotOrder is an order isomorphism from Fin(T) onto the positions u whose label sigma(u) is less than T. Assume cut deletes one position and its label using the two increasing finSuccAbove equivalences; lowWord reads sigma along slotOrder and identifies the low labels with Fin(T) using Fin.castLEOrderIso; and replace composes sigma with the low-label subtype permutation that sends lowWord sigma to the requested permutation rho. These assumptions are equalities of the actual operations at every size, not assumed inverse laws.")),
                    Paragraph(Text("Both conclusions hold. First, for every n and L with L at most n, every sigma on Fin(n plus one), every position t and every hypothesis sigma(t) less than L plus one, let so be slotOrder sigma at threshold L plus one and r be so.inverse(t). Then lowWord(cut sigma t) at threshold L equals cut(lowWord sigma at threshold L plus one) at r. Second, for every n and T with T at most n, every permutation S on Fin(n), and every rho on Fin(T), reading lowWord after replace S rho returns rho, and replacing once more by the original lowWord S returns S.")),
                    Paragraph(Text("Deleting t carries each surviving low slot through t.succAbove. This gives an order isomorphism onto the original low slots with t removed. Uniqueness of order isomorphisms between these finite chains identifies their enumerations. The row-label deletion follows the same increasing standardization. A low-label replacement preserves the set of low slots, so the same increasing enumeration reads the requested labels; applying the inverse low-label change restores the original permutation."))
                ), DescribeRole.Theorem)
        ), []));
}
