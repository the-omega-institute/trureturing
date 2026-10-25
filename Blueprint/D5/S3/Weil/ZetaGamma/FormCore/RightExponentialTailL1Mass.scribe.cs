using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class RightExponentialTailL1MassDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTailL1Mass.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp half-line L1 control and literal endpoint mass for the right exponential tail.",
        H("The actual positive-half-line L1 tail"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-right-tail-l1-integrable-and-mass"),
                DeclarationHandle.Create(Owner + "right_exponential_tail_l1_integrable_and_mass"),
                H("Outer-tail integrability and its exact mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every k>0 and every complex profile u integrable on t>0, the literal tail R_k u(t)=integral(exp(-k*s)*u(t+s),s>0) is integrable as a function of t>0. Its mass equals k^(-1)*(input mass - R_k u(0)). The full integrability statement and this actual endpoint term belong to the same theorem.")),
                    Paragraph(Text("The proof zero extends only the input for a whole-line L1 convolution. It computes the negative-half-line contribution as k^(-1)*R_k u(0), then subtracts that contribution from the whole-line convolution mass. No compact support, continuity, derivative, or vanishing endpoint is assumed.")),
                    Paragraph(Text("This identity organizes applications of existing convolution and change-of-variable results. It is used on the live upper-bound path of the optimal-constant theorem below; its endpoint is retained in full."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-right-tail-sharp-l1-constant"),
                DeclarationHandle.Create(Owner + "right_exponential_tail_l1_bound_iff"),
                H("The exact optimal uniform L1 constant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix k>0. A real number C bounds integral(norm(R_k u),t>0) by C*integral(norm(u),t>0) for every actual complex L1 input u if and only if C>=1/k. Thus the assertion quantifies over every input and every proposed constant.")),
                    Paragraph(Text("For the upper bound, apply the literal mass theorem to u and to its nonnegative norm profile. The norm of the actual complex tail is dominated by the real tail of that profile. Its nonnegative endpoint debit can be subtracted, giving the uniform bound 1/k.")),
                    Paragraph(Text("For the converse use the complete positive-scale family u_a(t)=exp(-a*t), a>0. These genuine half-line L1 inputs have input norm mass 1/a, actual tail exp(-a*t)/(k+a), and tail norm mass 1/(a*(k+a)). The ratio 1/(k+a) approaches 1/k as a decreases to zero. For any hypothetical smaller positive C, the scale a=(1/C-k)/2 gives a strict contradiction; one positive scale first rules out C<=0.")),
                    Paragraph(Text("The exponential family is noncompact. The optimality conclusion concerns the uniform bound, with no assertion that a nonzero input attains the limiting constant. This is a formal synthesis of classical convolution estimates and an explicit near-extremizing construction, without a literature originality claim."))),
                DescribeRole.Theorem))));
}
