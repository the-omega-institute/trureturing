using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class ZetaOrdinateReflectionTransferDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Same-height reflection cancels the first-order displacement from the critical line.",
        H("From complex zero sums to ordinate sums"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-reflection-bound"),
            DeclarationHandle.Create("D5/S3/Weil/ZeroData/ZetaOrdinateReflectionTransfer.actual_reflection_bound"),
            H("Quadratic reflection error"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Take every nontrivial zero with 0 < γ ≤ T, with its analytic multiplicity. "
                    + "At any real frequency v, the norm of the difference between the sums "
                    + "of exp(v(ρ − 1/2)) and exp(ivγ) is bounded by the multiplicity-weighted "
                    + "sum of d² exp(d), where d = |v(Re ρ − 1/2)|.")),
                Paragraph(Text(
                    "The reflection ρ ↦ 1 − conjugate(ρ) preserves height and multiplicity "
                    + "and reverses the displacement from the critical line. Averaging the "
                    + "original and reflected sums cancels the linear Taylor term. The "
                    + "exponential Taylor remainder bounds the resulting quadratic error.")),
                Paragraph(Text(
                    "A zero-density estimate uniform in displacement is a separate input "
                    + "for bounding the weighted error as T grows."))),
            DescribeRole.Theorem))));
}
