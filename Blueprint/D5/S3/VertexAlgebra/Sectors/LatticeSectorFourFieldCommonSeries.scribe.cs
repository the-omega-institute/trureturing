using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorFourFieldCommonSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldCommonSeries.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One numerator for twenty-four labelled words", H("One numerator for twenty-four labelled words"), Blocks(
            Describe.Lean(DescribeId.Create("latticesectorfourfieldcommonseries-actual-four-field-common-series"),
                DeclarationHandle.Create(Prefix + "actual_four_field_common_series"),
                H("One numerator for twenty-four labelled words"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Four original canonical lattice fields acting on an arbitrary fifth-sector state have one common generally infinite oscillator-valued power series after six-pair clearing and the original four canonical-on-input truncation shifts. A single locality order is chosen from the labelled fields before the fifth charge and state. Every permutation of the complete four-label list is covered, with modes -exponent-1 and labels attached to their original variables. This is the sector projection of the arbitrary-N ungraded local-word theorem; no new collision inference is part of this result. Bakalov--Kac, Matsuo--Nagatomo and Carnahan supplier conventions are retained."))), DescribeRole.Theorem))));
}
