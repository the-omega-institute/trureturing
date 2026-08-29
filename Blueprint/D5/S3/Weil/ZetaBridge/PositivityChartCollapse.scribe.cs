using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class PositivityChartCollapseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula omega = F.Id("Omega");
        Formula chart = F.Id("X");
        Formula measure = F.Id("nu");
        Formula features = F.Id("Phi");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula gamma = F.Id("gamma");
        Formula kernel = Seq(
            Open, x, Comma, Sp, y, Close, Sp, Mapsto, Sp,
            Int, Underscore, Grp(omega), Sp,
            features, Open, x, Close, Open, gamma, Close, Sp,
            F.Id("overline"), Open, features, Open, y, Close, Open, gamma, Close, Close,
            Sp, F.Id("d"), measure);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Every finite feature chart of one positive spectral measure has a positive "
                + "semidefinite Gram kernel.",
            H("Positivity-Chart Collapse"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("positive-spectral-measure-feature-chart-gram-positivity"),
                    DeclarationHandle.Create(
                        "D5/S3/Weil/ZetaBridge/PositivityChartCollapse."
                            + "positivity_chart_collapse"),
                    H("Feature dictionaries preserve Gram positivity"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, omega, Comma, Sp, chart, Colon, Sp,
                        Operatorname, Grp(F.Id("Type")), Comma, Sp,
                        Operatorname, Grp(F.Id("MeasurableSpace")), Open, omega, Close,
                        Sp, Land, Sp,
                        Operatorname, Grp(F.Id("Finite")), Open, chart, Close,
                        Comma, Sp,
                        measure, Colon, Sp, Operatorname, Grp(F.Id("Measure")), Open,
                        omega, Close, Comma, Sp,
                        features, Colon, Sp, chart, Sp, To, Sp,
                        Operatorname, Grp(F.Id("L2")), Open,
                        measure, Comma, Sp, Mathbb, Grp(F.Id("C")), Close,
                        Sp, Rightarrow, RowBreak,
                        Operatorname, Grp(F.Id("PosSemidef")), Open, kernel, Close))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let Omega be a measurable space, X a finite feature index type, nu "
                                + "a measure, and Phi a family of complex square-integrable "
                                + "features. The displayed kernel is defined directly by the "
                                + "source integral, with no separately declared kernel object.")),
                        Paragraph(Text(
                            "The matrix is the transpose of the standard complex Gram matrix. "
                                + "Mathlib proves that Gram matrix positive semidefinite; the local "
                                + "proof expands the L2 inner product and checks the conjugation "
                                + "orientation of the displayed integral."))),
                    DescribeRole.Theorem))));
    }
}
