using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants;

internal sealed class MidslopeCurvatureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "The harmonic and arithmetic midslope-curvature integrals have exact values.",
            H("Midslope Curvature"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("harmonic-midslope-curvature-vanishes"),
                    DeclarationHandle.Create("D5/S3/Constants/MidslopeCurvature.J_neg_one_eq_zero"),
                    H("The harmonic midslope curvature vanishes"),
                    StatementSource.FromAuthor(Disp(Seq(F.Id("J"), Open, Minus, D(1), Close, Eq, D(0), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                                            Paragraph(Text(
                                                "The definition uses the repository's harmonic power mean in the "
                                                + "producer-form integral. Twice that mean on the two half-scaled "
                                                + "symmetric inputs is 1 - t^2, so the bracket and hence the full "
                                                + "integrand vanish pointwise."))),
                    DescribeRole.Theorem
                ),
                Describe.Lean(
                    DescribeId.Create("arithmetic-midslope-curvature-is-minus-log-two"),
                    DeclarationHandle.Create("D5/S3/Constants/MidslopeCurvature.J_one_eq_neg_log_two"),
                    H("The arithmetic midslope curvature is minus log two"),
                    StatementSource.FromAuthor(Disp(Seq(F.Id("J"), Open, D(1), Close, Eq, Minus, Log, Sp, D(2), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                                            Paragraph(Text(
                                                "Twice the arithmetic mean on the two half-scaled symmetric inputs "
                                                + "is one. On the open unit interval the producer integrand therefore "
                                                + "reduces to -1 / (1 + t); endpoint-insensitive interval congruence "
                                                + "removes the exceptional displayed endpoint values. A unit shift "
                                                + "then turns the remaining integral into the reciprocal integral "
                                                + "from one to two, evaluated by mathlib's logarithmic integral."))),
                    DescribeRole.Theorem
                ))));
}
