using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.ChargedResidue;

internal sealed class SourceToQDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual charged residue comparison.",
        H("SourceToQ"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("charged-residue-source-to-q"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/ChargedResidue/SourceToQ.chargedGroundSource_to_Q"),
                H("The original source equals the actual Q field"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("For every original matching charged ground pair and signed lifts, the physical slice of the original source iterate equals the existing Q field on the actual tensor carrier, at every locality bound K at least the absolute pairing. Equality is proved coefficientwise from the actual inverse and public all-N source composition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-residue-sector-ground-pair"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/ChargedResidue/SourceToQ.charged_sector_ground_pair"),
                H("The matching-sector ground-pair supplier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("The complete source-to-Q equality, the independent source tail and shifted actual locality recover the full three-supported original-source coefficient law. This constructs SectorGroundPair for every lattice with unit determinant and every pair of projected charges, signs and matching signed lifts. Zero charges, rank zero, degenerate sectors and arbitrary oscillator inputs remain in scope. This supplies the ground-pair hypothesis of the existing sector propagation theorem."))),
                DescribeRole.Theorem))));
}
