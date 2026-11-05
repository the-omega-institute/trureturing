using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class RightExponentialTailL2Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual exponential-tail integration and a pointwise L2 estimate with the exact kernel norm.",
        H("The literal right tail on arbitrary half-line L2 inputs"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-right-tail-l2-integrable-and-bound"),
            DeclarationHandle.Create(
                "D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTailL2."
                    + "right_exponential_tail_l2_integrable_and_sq_le"),
            H("Actual Bochner integrability and the translated tail mass"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For k>0 and any complex profile in L2 on the positive half-line, "
                        + "the literal integral R_k u(t)=integral(exp(-k*s)*u(t+s),s>0) "
                        + "is Bochner integrable at every t>=0. Its squared magnitude "
                        + "is at most integral(|u(x)|^2,x>t)/(2*k). No continuity or "
                        + "compact support of the input is assumed.")),
                Paragraph(Text(
                    "The proof translates the half-line L2 input by using its zero "
                        + "extension for membership. The exponential kernel has squared "
                        + "L2 norm exactly 1/(2*k); Holder at exponent 2 proves product "
                        + "integrability and the bound. The estimate keeps the actual "
                        + "translated tail mass rather than replacing it with a formal "
                        + "operator norm or an abstract extension.")),
                Paragraph(Text(
                    "This estimate supplies actual pointwise and endpoint control for "
                        + "weighted completion arguments. It does not itself establish "
                        + "a complete weighted energy identity, the arithmetic debit, "
                        + "or the positivity required for RH."))),
            DescribeRole.Theorem))));
}
