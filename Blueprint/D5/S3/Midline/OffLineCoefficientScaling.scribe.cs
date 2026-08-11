using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline;

internal sealed class OffLineCoefficientScalingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Midline/OffLineCoefficientScaling",
            "Off-line coefficients split into density, phase, and scaling factors."),
        H("Off-Line Coefficient Scaling"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("off-line-coefficient-scaling-spec"),
                H("Coefficients split into density, phase, and scaling factors"),
                LeanTheorem(
                    "D5/S3/Midline/OffLineCoefficientScaling."
                    + "off_line_coefficient_scaling_spec"),
                Disp(Seq(
                    F.Id("s"), Eq, Frac, Grp(D(1)), Grp(D(2)), Plus, Delta, Plus,
                    F.Id("i"), F.Id("t"), Comma, Quad, Sp,
                    F.Id("e"), Caret, Grp(Minus, F.Id("s"), Ell), Eq,
                    F.Id("e"), Caret, Grp(Minus, Frac, Grp(D(1)), Grp(D(2)), Ell),
                    Cdot, Sp, F.Id("e"), Caret, Grp(Minus, F.Id("i"), F.Id("t"), Ell),
                    Cdot, Sp, F.Id("e"), Caret, Grp(Minus, Delta, Ell), Comma, Quad,
                    Operatorname, Grp(F.Id("scalingLedger")), Eq, Delta, Ell, Dot)),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "For a spectral parameter with real displacement `delta`, each "
                        + "labeled coefficient factors into its critical half-density, "
                        + "unitary phase, and real scaling terms. The scaling ledger is "
                        + "exactly `delta * length`; when `delta` is nonzero the existing "
                        + "growth theorem supplies nonvanishing, common sign, natural "
                        + "scaling, and unboundedness on every positive-length address.")),
                    Paragraph(Text(
                        "Multiplication by any complex unit preserves the coefficient's "
                        + "norm. These are coordinatewise statements only and do not assert "
                        + "anything about cancellation after analytic continuation."))))),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Midline/OffLineScaling")),
        ]));
}
