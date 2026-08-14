using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline;

internal sealed class HeatTraceHolomorphyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A heat trace is analytic throughout the open half-plane to the right of its heat abscissa.",
        H("Heat-Trace Holomorphy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("heat-trace-is-analytic-on-its-convergence-half-plane"),
                DeclarationHandle.Create(
                    "D5/S3/Midline/HeatTraceHolomorphy.heat_trace_analyticOnNhd_of_abscissa"),
                H("The heat trace is analytic on its convergence half-plane"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("IsHeatAbscissa")), Open,
                    F.Id("M"), Comma, Sp, Alpha, Close, Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("a"), Comma, Sp,
                    D(0), Sp, Le, Sp, F.Id("M"), Open, F.Id("a"), Close, Close, Sp,
                    Rightarrow, Sp,
                    Operatorname, Grp(F.Id("AnalyticOnNhd")), Underscore,
                    Grp(Mathbb, Grp(F.Id("C"))), Open,
                    Operatorname, Grp(F.Id("heatTrace")), Open, F.Id("M"), Close,
                    Comma, Sp, OpenBrace, F.Id("s"), InMacro, Sp,
                    Mathbb, Grp(F.Id("C")), Mid, Sp, Alpha, Sp, Lt, Sp,
                    Re, Open, F.Id("s"), Close, CloseBrace, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At each point in the convergence half-plane, choose a strictly intermediate real abscissa. The heat-abscissa hypothesis supplies a summable exponential majorant on that smaller right half-plane, so the Weierstrass M-test gives differentiability there and hence analyticity at the chosen point."))),
                DescribeRole.Theorem))));
}
