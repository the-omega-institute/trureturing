using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Counting;

internal sealed class IdealCongruenceCountRealScaleDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Effective coset lattice-point count.",
        H("Effective coset lattice-point count"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-card-coset-inter-smul-sub-volume-mul-rpow-le"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Lattices/Counting/IdealCongruenceCountRealScale.exists_card_coset_inter_smul_sub_volume_mul_rpow_le"),
                H("Effective coset lattice-point count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Effective coset lattice-point count (Widmer / GRS Theorem 3 as used; the translate- " +
                    "and-transport closure of L1). For a full lattice T '' ℤ^ι (T a linear automorphism of " +
                    "ι → ℝ) and a bounded measurable region D whose frontier is covered by finitely many " +
                    "Lipschitz images of the unit cube, the number of points of any coset ξ + T '' ℤ^ι in " +
                    "the real dilation t • D is vol D / |det T| · t ^ d + O(t ^ (d-1)), with the implied " +
                    "constant uniform in the translate ξ (it depends only on the cover data and T, as the " +
                    "L1 constant depends only on the cover data)."))),
                DescribeRole.Theorem)
        )));
}
