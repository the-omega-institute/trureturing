using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.HalfFock;
internal sealed class OriginalHalfCurrentCauchyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary coefficients of the regular half-current correction",
        H("Chamber expansion and the removable diagonal"), Blocks(
        Describe.Lean(DescribeId.Create("original-half-current-cauchy-regular-series"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentCauchy.regularSeries"),
            H("Regular Cauchy correction series"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
            Blocks(Paragraph(Text("The normalized roots b and c of 1-eta*u and 1-eta*v have constant term one. The regular chamber expression is eta*(1+b*c)/(2*b*c*(b+c)^2). The second variable is expanded first with Laurent coefficients in the first variable."))),
            DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("original-half-current-cauchy-coefficient"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentCauchy.regular_series_coefficient"),
            H("Every ordinary bivariate coefficient"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
            Blocks(Paragraph(Text("Multiplying the dressed and undressed chamber expansions by (u-v)^2 clears their denominators. The square-root relations then identify their difference with the regular expression. For a fixed inner coefficient q, substitution uses only powers zero through q. Nonnegative outer coefficients of the original chamber kernel vanish, so the contraction sum gives the ordinary coefficient of the regular difference."))),
            DescribeRole.Theorem)))));
}
