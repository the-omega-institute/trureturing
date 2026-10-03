using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimeIdeals.NormResidue;

internal sealed class IdealCongruenceCountCellsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Effective count of cone points of idealSet K J with a norm residue.",
        H("Effective count of cone points of idealSet K J with a norm residue"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-card-ideal-set-residue-le"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountCells.exists_card_idealSet_residue_le"),
                H("Effective count of cone points of idealSet K J with a norm residue"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Effective count of cone points of idealSet K J with a norm residue (the Widmer / GRS " +
                    "geometric core). For a fixed nonzero ideal J, a modulus m and a residue b, the number " +
                    "of cone points a ∈ idealSet K J of mixedEmbedding.norm ≤ N·N(J) whose integer norm " +
                    "intNorm (idealSetEquiv K J a) is ≡ b (mod m) is κ·N + O(N^{1-1/d}), d = [K:ℚ]. This " +
                    "is the substantive analytic input."))),
                DescribeRole.Theorem)
        )));
}
