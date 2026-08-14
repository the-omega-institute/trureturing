using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.ToySpectrum;

internal sealed class FourPointPowerDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four symmetric exponential points have a hyperbolic-trigonometric power defect.",
        H("Four-Point Power Defect"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("four-point-power-defect-identity"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ToySpectrum/FourPointPowerDefect.four_point_power_defect_eq"),
                H("The four power defects collapse to a real product"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Defect")), Open,
                    F.Id("q"), Comma, Sp, Theta, Comma, Sp, F.Id("k"), Close,
                    Sp, Eq, Sp, D(4), Cdot, Open, D(1), Sp, Minus, Sp,
                    Operatorname, Grp(F.Id("cosh")), Open,
                    F.Id("k"), F.Id("q"), Close, Cdot,
                    Operatorname, Grp(F.Id("cos")), Open,
                    F.Id("k"), Theta, Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For real q and theta, the four points are exp(q + i theta), "
                        + "exp(q - i theta), exp(-q + i theta), and exp(-q - i theta). "
                        + "Defect(q, theta, k) is the sum of 1 - z^k over these points.")),
                    Paragraph(Text(
                        "The power-of-exponential identity moves k into each exponent. "
                        + "The two angular signs cancel the sine terms, while the two radial "
                        + "signs combine into twice the hyperbolic cosine.")),
                    Paragraph(Text(
                        "This records only the four-point algebraic identity from the source atom. "
                        + "Its detection estimate, asymptotic formula, reciprocal-power expansion, "
                        + "measure interpretation, and numerical certificates are not claimed."))),
                DescribeRole.Theorem)),
        []));
}
