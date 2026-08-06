using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants;

internal sealed class MidslopeCurvatureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S3/Constants/MidslopeCurvature",
                "The harmonic and arithmetic midslope-curvature integrals have exact values."),
            H("Midslope Curvature"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("harmonic-midslope-curvature-vanishes"),
                    H("The harmonic midslope curvature vanishes"),
                    LeanTheorem(
                        "D5/S3/Constants/MidslopeCurvature.J_neg_one_eq_zero"),
                    Disp(Seq(F.Id("J"), Open, Minus, D(1), Close, Eq, D(0), Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text(
                            "The definition uses the repository's harmonic power mean in the "
                            + "producer-form integral. Twice that mean on the two half-scaled "
                            + "symmetric inputs is 1 - t^2, so the bracket and hence the full "
                            + "integrand vanish pointwise.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("arithmetic-midslope-curvature-is-minus-log-two"),
                    H("The arithmetic midslope curvature is minus log two"),
                    LeanTheorem(
                        "D5/S3/Constants/MidslopeCurvature.J_one_eq_neg_log_two"),
                    Disp(Seq(F.Id("J"), Open, D(1), Close, Eq, Minus, Log, Sp, D(2), Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text(
                            "Twice the arithmetic mean on the two half-scaled symmetric inputs "
                            + "is one. On the open unit interval the producer integrand therefore "
                            + "reduces to -1 / (1 + t); endpoint-insensitive interval congruence "
                            + "removes the exceptional displayed endpoint values. A unit shift "
                            + "then turns the remaining integral into the reciprocal integral "
                            + "from one to two, evaluated by mathlib's logarithmic integral.")))
                ))));
}
