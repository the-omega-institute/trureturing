using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Haar;

internal sealed class HaarColumnChartDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Haar Column Chart", H("Haar Column Chart"),
        Blocks(
            Paragraph(Text("Splitting a skew matrix into one column and block; Jacobian of column chart.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Haar/HaarColumnChart.abs_det_logDerivU_col_eq_cayleyDensity"),
                H("abs_det_logDerivU_col_eq_cayleyDensity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For the family θ ↦ Cayley chart of U(n) at skewColumnEquiv k₀ (θ,0), the form g⁻¹dg read in the column coordinates has absolute determinant the Cayley weight cayleyDensity (J = 1) at that point.")))))));
}
