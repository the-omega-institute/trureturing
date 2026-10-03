using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimeIdeals.NormResidue;

internal sealed class IdealCongruenceCountCellGeometryDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Effective residue count in an orthant cell.",
        H("Effective residue count in an orthant cell"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-card-residue-fibre-sub-mul-rpow-le-explicit"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountCellGeometry.exists_card_residue_fibre_sub_mul_rpow_le_explicit"),
                H("Effective residue count in an orthant cell"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Fix a real-sign orthant and a lattice coset. The number of cone points in that " +
                    "cell with a prescribed norm residue differs from its explicit volume term by " +
                    "at most C times the dilation to degree d - 1. The leading term is zero when " +
                    "the cell does not carry the prescribed residue."))),
                DescribeRole.Theorem)
        )));
}
