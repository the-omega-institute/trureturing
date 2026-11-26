using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence.ConditionalExpansion;

internal sealed class BellKernelLimitDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Divergence/ConditionalExpansion/BellKernelLimit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Bell-kernel overlap controls the limit of actual conditional trace-gap ratios.",
        H("Bell-kernel limit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bell-kernel-positive-trace-limit"),
                DeclarationHandle.Create(Module + "bell_kernel_limit"),
                H("Right-hand limit of the positive trace"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let B₀ and X₀ be positive semidefinite matrices and Q the orthogonal "
                    + "projection onto the kernel of B₀. As ε decreases to zero through "
                    + "positive values, the trace of the positive part of εX₀ − B₀ "
                    + "divided by ε tends to the real trace of QX₀. The lower estimate "
                    + "tests with Q. The upper estimate uses the inverse square root on "
                    + "the support of B₀ to control the complementary compression and "
                    + "bounds the mixed terms by a positive matrix square."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bell-kernel-conditional-ratio"),
                DeclarationHandle.Create(Module + "exists_bell_kernel_ratio_le"),
                H("Conditional ratios near the Bell-kernel overlap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite channel N with input dimension d ≥ 2, let P be the "
                    + "normalized Bell projector. Take B₀ = amp N(I − P), X₀ = amp N(P), "
                    + "and Q the projection onto the kernel of B₀. For each positive "
                    + "tolerance there are two orthogonal density states on Option A × A "
                    + "with strictly positive input gap at parameter one. Their actual "
                    + "output-to-input conditional gap ratio is at most the real trace "
                    + "of QX₀ plus the tolerance. The padded Bell pair realizes the "
                    + "positive-trace quotient for a sufficiently small ε."))),
                DescribeRole.Theorem))));
}
