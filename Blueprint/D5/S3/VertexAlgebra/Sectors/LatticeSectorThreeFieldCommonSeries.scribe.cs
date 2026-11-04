using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorThreeFieldCommonSeriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeSectorThreeFieldCommonSeries", H("LatticeSectorThreeFieldCommonSeries"), Blocks(
            Describe.Lean(DescribeId.Create("latticesectorthreefieldcommonseries-labelledfields"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorThreeFieldCommonSeries.labelledFields"),
                H("labelledFields"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The labelledFields coefficient construction uses the displayed signed indices and finite polynomial fibers, with exactly the assumptions of its Lean statement."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latticesectorthreefieldcommonseries-nestedcanonical"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorThreeFieldCommonSeries.nestedCanonical"),
                H("nestedCanonical"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The nestedCanonical coefficient construction uses the displayed signed indices and finite polynomial fibers, with exactly the assumptions of its Lean statement."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latticesectorthreefieldcommonseries-actual-three-field-common-series"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorThreeFieldCommonSeries.actual_three_field_common_series"),
                H("actual_three_field_common_series"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary even integral symmetric lattice data and arbitrary descendants, all six signed canonical products share the same generally infinite series. The pair locality order precedes the fourth charge and state; monomial bounds come from their actual truncation."))), DescribeRole.Theorem))));
}
