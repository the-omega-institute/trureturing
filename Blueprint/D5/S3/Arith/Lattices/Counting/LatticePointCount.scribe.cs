using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Counting;

internal sealed class LatticePointCountDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Count ↔ volume bridge.",
        H("Count ↔ volume bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("abs-card-inter-sub-volume-mul-pow-le"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Lattices/Counting/LatticePointCount.abs_card_inter_sub_volume_mul_pow_le"),
                H("Count ↔ volume bridge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Count ↔ volume bridge. The number of points of n⁻¹ℤ^ι in a bounded measurable s " +
                    "differs from vol(s)·nᵈ by at most the number of grid cells meeting ∂s. This is the " +
                    "effective form of the sandwich behind tendsto_card_div_pow_atTop_volume."))),
                DescribeRole.Theorem)
        )));
}
