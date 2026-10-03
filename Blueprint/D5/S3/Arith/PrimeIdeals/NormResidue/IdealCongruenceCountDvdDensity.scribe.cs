using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimeIdeals.NormResidue;

internal sealed class IdealCongruenceCountDvdDensityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The dvd-density is the full density divided by N(𝔟) (Lang VI §3 Thm 3; GRS Thm 1).",
        H("The dvd-density is the full density divided by N(𝔟) (Lang VI §3 Thm 3; GRS Thm 1)"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("card-norm-le-residue-class-dvd-div-density"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountDvdDensity.cardNormLeResidueClassDvd_div_density"),
                H("The dvd-density is the full density divided by N(𝔟) (Lang VI §3 Thm 3; GRS Thm 1)"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The dvd-density is the full density divided by N(𝔟) (Lang VI §3 Thm 3; GRS Thm 1). " +
                    "For a realizer 𝔟 with N(𝔟) (mod c) a unit, the 𝔟-divisible class-D norm-residue count " +
                    "has density κfull/N(𝔟), where κfull is the full class-D residue-y density. Proved the " +
                    "geometric (covolume / CRT-equidistribution) way: principalize both counts at a " +
                    "coprime representative J of D⁻¹ and read off the index-N(𝔟) sublattice scaling from " +
                    "the shared cone estimate exists_card_idealSet_residue_real_le_dvd."))),
                DescribeRole.Theorem)
        )));
}
