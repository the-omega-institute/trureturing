using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Entire;

internal sealed class DirectionalExponentialTypeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real-axis boundedness directs exponential growth into the imaginary coordinate.", H("Directional exponential type"),
        Blocks(
            Describe.Lean(DescribeId.Create("directional-exponential-type-norm-le-exp-abs-im"),
                DeclarationHandle.Create("D5/S3/Analytic/Entire/DirectionalExponentialType.norm_le_exp_abs_im"),
                H("Exact directional bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let an entire function F have real-axis bound B and radial bound C times (1 + |z|) to the power m times exp(a |z|), with a nonnegative. Its norm is bounded by max(B,C) times (1 + |z|) to the power m times exp(a |Im z|). In each half-plane the quotient by (1 minus or plus iz) to the power m cancels the polynomial growth on the imaginary ray, while an exponential factor cancels the exact radial rate on that ray. The four Phragmen-Lindelof quadrant theorems bound the two quotients. Recovering the original function preserves both a and m."))),
                DescribeRole.Theorem))));
}
