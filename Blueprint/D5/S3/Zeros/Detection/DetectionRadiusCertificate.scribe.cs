using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Detection;

internal sealed class DetectionRadiusCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The beta 0.51 and gamma 10^12 detection radius is exactly 10^1200.",
        H("Exact Detection-Radius Certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("detection-radius-ten-to-the-1200-certificate"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Detection/DetectionRadiusCertificate."
                    + "detection_radius_ten_to_the_1200_certificate"),
                H("The specialized detection radius is exactly 10^1200"),
                StatementSource.FromAuthor(Disp(Seq(
                    Frac,
                    Grp(Log, Sp, D(1, 0), Caret, Grp(D(1, 2))),
                    Grp(
                        Frac, Grp(D(5, 1)), Grp(D(1, 0, 0)),
                        Minus, Frac, Grp(D(1)), Grp(D(2))),
                    Sp, Eq, Sp, D(1, 2, 0, 0), Sp, Log, Sp, D(1, 0),
                    Sp, Land, Sp,
                    Exp, Sp, Open,
                    Frac,
                    Grp(Log, Sp, D(1, 0), Caret, Grp(D(1, 2))),
                    Grp(
                        Frac, Grp(D(5, 1)), Grp(D(1, 0, 0)),
                        Minus, Frac, Grp(D(1)), Grp(D(2))),
                    Close, Sp, Eq, Sp, D(1, 0), Caret, Grp(D(1, 2, 0, 0))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The atom gives the visibility-scale reading ln(gamma)/(beta - 1/2). "
                        + "For the exact inputs beta = 51/100 and gamma = 10^12, Lean proves "
                        + "that this logarithmic scale is 1200 log 10 and that its exponential "
                        + "is exactly 10^1200.")),
                    Paragraph(Text(
                        "The denominator is checked separately as the nonzero rational 1/100. "
                        + "The proof uses pinned Mathlib's logarithm-of-a-power and exponential-"
                        + "of-logarithm identities; no decimal approximation is used.")),
                    Paragraph(Text(
                        "The source writes the general visibility law with an approximation "
                        + "sign. This theorem certifies only its displayed beta = 0.51 and "
                        + "gamma = 10^12 arithmetic specialization exactly; it does not turn "
                        + "the surrounding approximate model into a universal exact law."))),
                DescribeRole.Theorem)),
        []));
}
