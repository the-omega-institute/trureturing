// SOURCE_ONLY / UNCOMPILED, 2026-10-25.
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class RightExponentialTailL1MassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal exponential-tail integrability and mass, retaining the endpoint trace.",
        H("The actual positive-half-line L1 tail mass"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-right-tail-l1-integrable-and-mass"),
            DeclarationHandle.Create(
                "D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTailL1Mass."
                    + "right_exponential_tail_l1_integrable_and_mass"),
            H("Outer-tail integrability and its exact mass"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every k>0 and every complex profile u integrable on t>0, the literal tail R_k u(t)=integral(exp(-k*s)*u(t+s),s>0) is integrable as a function of t>0. Its mass equals k^(-1)*(input mass - R_k u(0)). The full integrability statement and this actual endpoint term belong to the same theorem.")),
                Paragraph(Text("The proof zero extends only the input for a whole-line L1 convolution. It computes the negative-half-line contribution as k^(-1)*R_k u(0), then subtracts that contribution from the whole-line convolution mass. No compact support, continuity, derivative, or vanishing endpoint is assumed.")),
                Paragraph(Text("The input and output are the original complex-valued functions and actual Bochner integrals. The formula supplies the endpoint debit used in subsequent half-line balances."))),
            DescribeRole.Theorem))));
}

