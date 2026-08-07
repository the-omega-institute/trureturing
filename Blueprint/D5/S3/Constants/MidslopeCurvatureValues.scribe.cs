using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants;

internal sealed class MidslopeCurvatureValuesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S3/Constants/MidslopeCurvatureValues",
                "The remaining rationalizable midslope-curvature integrals have exact values."),
            H("Midslope Curvature Values"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("negative-half-is-half-the-geometric-value"),
                    H("The negative-half value is half the geometric value"),
                    LeanTheorem(
                        "D5/S3/Constants/MidslopeCurvatureValues.J_neg_half_eq_half_J_zero"),
                    Disp(Seq(
                        F.Id("J"), Open, Minus, Frac, Grp(D(1)), Grp(D(2)), Close, Eq,
                        Frac, Grp(F.Id("J"), Open, D(0), Close), Grp(D(2)), Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text(
                            "On the open unit interval, twice the negative-half mean is two "
                            + "times 1 - t squared divided by one plus its square root. The "
                            + "resulting bracket is exactly half the geometric-mean bracket, "
                            + "so interval-integral linearity proves the relation without first "
                            + "evaluating either integral.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("geometric-value-is-one-minus-two-log-two"),
                    H("The geometric value is one minus two log two"),
                    LeanTheorem(
                        "D5/S3/Constants/MidslopeCurvatureValues.J_zero_eq_one_sub_two_log_two"),
                    Disp(Seq(
                        F.Id("J"), Open, D(0), Close, Eq, D(1), Minus, D(2), Sp, Log, Sp, D(2),
                        Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text(
                            "The producer integrand first reduces to minus one divided by the "
                            + "product of 1 + t and 1 + sqrt(1 - t squared). The substitution "
                            + "t = 2u / (1 + u squared) rationalizes it to 1 - 2 / (1 + u) on "
                            + "the unit interval. Mathlib's reciprocal integral then supplies "
                            + "the logarithm.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("half-power-value-is-five-sixths-minus-two-log-two"),
                    H("The half-power value is five sixths minus two log two"),
                    LeanTheorem("D5/S3/Constants/MidslopeCurvatureValues.J_half_eq"),
                    Disp(Seq(
                        F.Id("J"), Open, Frac, Grp(D(1)), Grp(D(2)), Close, Eq, Frac,
                        Grp(D(5), Minus, D(1, 2), Sp, Log, Sp, D(2)), Grp(D(6)), Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text(
                            "Twice the half-power mean is one half of 1 + sqrt(1 - t squared). "
                            + "The same rationalizing substitution turns the producer integrand "
                            + "into -u squared / 2 + u + 1 / 2 - 2 / (1 + u), whose polynomial "
                            + "and reciprocal parts integrate exactly.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("half-power-value-is-an-affine-combination"),
                    H("The half-power value is an affine combination"),
                    LeanTheorem("D5/S3/Constants/MidslopeCurvatureValues.J_half_eq_affine"),
                    Disp(Seq(
                        F.Id("J"), Open, Frac, Grp(D(1)), Grp(D(2)), Close, Eq,
                        Frac, Grp(D(5)), Grp(D(6)), F.Id("J"), Open, D(0), Close, Plus,
                        Frac, Grp(D(1)), Grp(D(3)), F.Id("J"), Open, D(1), Close, Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text(
                            "Substituting the exact half-power and geometric values together "
                            + "with the frozen arithmetic value reduces the relation to a ring "
                            + "identity in 1 and log 2.")))
                ))));
}
