using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Dilation;

internal sealed class MellinDilationFlowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mellin is Fourier in logarithmic time along the dilation flow.",
        H("Mellin Transform on the Dilation Flow"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mellin-transform-is-fourier-on-the-dilation-flow"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Dilation/MellinDilationFlow.mellin_eq_fourier_on_dilation_flow"),
                H("Mellin is Fourier in logarithmic time"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("f"), Colon, Mathbb, Grp(F.Id("R")), Sp, To, Sp,
                    Mathbb, Grp(F.Id("C")), Comma, Sp,
                    Forall, Sp, F.Id("s"), InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma, Sp,
                    Operatorname, Grp(F.Id("mellin")), Open, F.Id("f"), Comma, F.Id("s"),
                    Close, Sp, Eq, Sp,
                    Int, Underscore, Grp(Mathbb, Grp(F.Id("R"))),
                    Exp, Open, F.Id("i"), Sp, Operatorname, Grp(F.Id("Im")),
                    Open, F.Id("s"), Close, F.Id("t"), Close, Sp, Cdot, Sp,
                    Exp, Open, Re, Open, F.Id("s"), Close, F.Id("t"), Close, Sp, Cdot, Sp,
                    F.Id("f"), Open, Exp, Open, F.Id("t"), Close, Close, Thin, F.Id("dt"),
                    Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Set x = exp(t), so dx contributes exp(t). The original Mellin factor "
                        + "x^(s-1) combines with that Jacobian to give exp(s t). Splitting the "
                        + "complex exponential exposes exp(Re(s)t) as the dilation weight and "
                        + "exp(i Im(s)t) as its Fourier phase.")),
                    Paragraph(Text(
                        "Pinned Mathlib already proves the stronger bridge `mellin_eq_fourier` "
                        + "in the reflected coordinate u = -t. The Lean proof reuses that theorem "
                        + "and Fourier reflection to obtain the displayed t = log(x) orientation; "
                        + "it does not reprove change of variables.")),
                    Paragraph(Text(
                        "The identity is unconditional because Mathlib totalizes nonintegrable "
                        + "Bochner integrals. A checked compact nonzero window witnesses "
                        + "MellinConvergent at s = 1 and makes the displayed integrand equal one "
                        + "at logarithmic time zero."))),
                DescribeRole.Theorem)),
        []));
}
