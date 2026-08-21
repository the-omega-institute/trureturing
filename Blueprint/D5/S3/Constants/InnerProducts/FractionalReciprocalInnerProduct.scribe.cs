using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.InnerProducts;

internal sealed class FractionalReciprocalInnerProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fractional-reciprocal vector has an exact unit-interval inner product.",
        H("Fractional-Reciprocal Inner Product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fractional-reciprocal-inner-product"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/InnerProducts/FractionalReciprocalInnerProduct."
                        + "fractional_reciprocal_inner_product"),
                H("The fractional-reciprocal inner product has an exact Euler value"),
                StatementSource.FromAuthor(Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The carrier is the real L2 space on the positive half-line. The first "
                            + "vector is the indicator of the open unit interval, and the second "
                            + "is the L2 class of x mapped to fract(1/(a x)). A positive integer "
                            + "is transported through its equal natural representative, and both "
                            + "vectors are constructed from those source functions.")),
                    Paragraph(Text(
                        "Square integrability follows from boundedness near zero and reciprocal-"
                            + "square decay after one. A reciprocal change of variables reduces "
                            + "the inner product to the fractional-part tail integral.")),
                    Paragraph(Text(
                        "The intervals from n+1 to n+2 identify that tail directly with Mathlib's "
                            + "ZetaAsymptotics.term series. Its exact sum is one minus the "
                            + "Euler-Mascheroni constant; the initial interval contributes log a."))),
                DescribeRole.Theorem))));

    private static Formula Formula()
    {
        Formula a = F.Id("a");
        return Disp(Seq(
            Forall, Sp, a, InMacro, Mathbb, Grp(F.Id("Z")), Comma, Sp,
            D(1), Sp, Leq, Sp, a, Sp, Rightarrow, Sp,
            Langle, Operatorname, Grp(F.Id("unitIntervalIndicator")), Comma, Sp,
            Operatorname, Grp(F.Id("integerFractionalReciprocal")), Open, a, Close,
            Rangle, Underscore, Grp(F.Id("L"), Caret, D(2), Open,
                D(0), Comma, Infty, Close), Sp, Eq, Sp,
            Frac,
            Grp(Log, Sp, a, Sp, Plus, Sp, D(1), Sp, Minus, Sp, GammaLower),
            Grp(a), Dot));
    }
}
