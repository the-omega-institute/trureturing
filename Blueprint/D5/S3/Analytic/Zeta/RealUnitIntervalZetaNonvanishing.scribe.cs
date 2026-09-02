using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class RealUnitIntervalZetaNonvanishingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Riemann zeta is nonzero at every real point strictly between zero and one.",
        H("Real Unit-Interval Zeta Nonvanishing"),
        Blocks(Describe.Lean(
            DescribeId.Create("riemann-zeta-is-nonzero-on-the-open-real-unit-interval"),
            DeclarationHandle.Create(
                "D5/S3/Analytic/Zeta/RealUnitIntervalZetaNonvanishing."
                    + "riemannZeta_ne_zero_on_real_unit_interval"),
            H("Riemann zeta is nonzero on the open real unit interval"),
            StatementSource.FromAuthor(Disp(Seq(
                Forall, Sp, F.Id("sigma"), InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Esc,
                D(0), Lt, F.Id("sigma"), Sp, Land, Sp, F.Id("sigma"), Lt, D(1),
                Sp, Rightarrow, Sp, Zeta, Open, F.Id("sigma"), Close, Sp, Neq, Sp, D(0)))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The proof pairs adjacent terms of the alternating Dirichlet series. "
                        + "Uniform convergence on compact subsets of the positive half-plane "
                        + "makes the paired series analytic, and the identity principle "
                        + "identifies it with the eta factor times Riemann zeta.")),
                Paragraph(Text(
                    "At a positive real argument every adjacent pair is strictly positive. "
                        + "The eta factor therefore cannot vanish; for an argument below one, "
                        + "this forces the zeta value to be nonzero. Pinned Mathlib provides "
                        + "the series and analytic ingredients but no theorem with this open "
                        + "real-interval conclusion."))),
            DescribeRole.Theorem))));
}
