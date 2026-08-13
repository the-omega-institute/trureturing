using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline;

internal sealed class HeatTraceConvergenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boundary-divergent heat abscissas give exact ordinary complex summability thresholds, with golden and prime-axis specializations.",
        H("Ordinary Heat-Coefficient Convergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("boundary-divergence-gives-the-ordinary-summability-threshold"),
                DeclarationHandle.Create(
                    "D5/S3/Midline/HeatTraceConvergence.heat_coefficient_summable_iff_of_boundary_divergent"),
                H("Boundary divergence gives the ordinary summability threshold"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("BoundaryDivergentAbscissa")), Open,
                    F.Id("M"), Comma, Sp, Alpha, Close, Sp, Rightarrow, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Summable")), Open,
                    Operatorname, Grp(F.Id("heatCoefficient")), Open,
                    F.Id("M"), Comma, Sp, F.Id("s"), Close, Close, Sp,
                    Leftrightarrow, Sp, Alpha, Sp, Lt, Sp, Re, Open, F.Id("s"), Close,
                    CloseBracket, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Norm summability reduces ordinary complex summability to the real heat series. The two strict abscissa clauses and boundary divergence then give the exact right-half-plane criterion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-heat-coefficients-have-the-golden-abscissa-threshold"),
                DeclarationHandle.Create(
                    "D5/S3/Midline/HeatTraceConvergence.golden_heat_coefficient_summable_iff"),
                H("Golden heat coefficients have the golden-abscissa threshold"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), Colon, Sp, Mathbb, Grp(F.Id("C")), Comma, Sp,
                    Operatorname, Grp(F.Id("Summable")), Open,
                    Operatorname, Grp(F.Id("heatCoefficient")), Open,
                    F.Id("goldenSpectrum"), Comma, Sp, F.Id("s"), Close, Close, Sp,
                    Leftrightarrow, Sp, Frac, Grp(D(1)),
                    Grp(Varphi, Caret, Grp(D(2))), Sp, Lt, Sp,
                    Re, Open, F.Id("s"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The universal criterion specializes at the boundary-divergent golden heat abscissa one over phi squared."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-axis-heat-coefficients-have-threshold-one"),
                DeclarationHandle.Create(
                    "D5/S3/Midline/HeatTraceConvergence.prime_axis_heat_coefficient_summable_iff"),
                H("Prime-axis heat coefficients have threshold one"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), Colon, Sp, Mathbb, Grp(F.Id("C")), Comma, Sp,
                    Operatorname, Grp(F.Id("Summable")), Open,
                    Operatorname, Grp(F.Id("heatCoefficient")), Open,
                    F.Id("primeAxisLogLength"), Comma, Sp, F.Id("s"), Close, Close, Sp,
                    Leftrightarrow, Sp, D(1), Sp, Lt, Sp,
                    Re, Open, F.Id("s"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The same criterion specializes at the boundary-divergent prime-axis logarithmic abscissa one."))),
                DescribeRole.Theorem))));
}
