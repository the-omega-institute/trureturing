using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator.TranslationEnergy.Unit;

internal sealed class WidthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Width of the rounded unit aggregate.",
        H("Width of the rounded unit aggregate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unit-width-unit-cell-width"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/Unit/Width.unit_cell_width"),
                H("The integrand width"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive natural R and every ordered rational cell of length ell, the actual rounded unit payload at precision m and Taylor depth 4m+4 has norm-square interval width at most 72 ell/R+16*2^-m+16*2^-32. The cutoff intervals stay in [0,1] after outward rounding, so each signed difference lies in [-1,1]."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unit-width-unit-aggregate-width"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/Unit/Width.unit_aggregate_width"),
                H("The full aggregate width"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every rational shift and mesh depth d, let L be the actual support hull length. Summing the cell bounds gives aggregate width at most (72/R)(L/2^d)L+(16*2^-m+16*2^-32)L. This uses the actual mapped payload list, total length and squared-length bound."))),
                DescribeRole.Theorem)),
        []));
}
