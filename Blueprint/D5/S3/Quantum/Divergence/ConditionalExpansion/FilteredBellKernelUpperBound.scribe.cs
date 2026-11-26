using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence.ConditionalExpansion;

internal sealed class FilteredBellKernelUpperBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The inverse filter determines the Bell-kernel upper bound on conditional expansion.",
        H("Bell-kernel upper bound for filtered channels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("filtered-channel-bell-upper-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredBellKernelUpperBound."
                    + "filtered_channel_bell_upper_bound"),
                H("Upper bound from the inverse marginal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let G be a positive definite filter on A ⊗ E normalized by "
                    + "Tr_E G / e = I, with d = dim A ≥ 2 and e = dim E > 0. "
                    + "Set M = Tr_A(G⁻¹) / d. The conditional expansion of the filtered "
                    + "channel is at most Tr(M⁻¹) / e for every hockey-stick parameter "
                    + "γ ≥ 1, with either choice of orthogonality restriction. The kernel "
                    + "projection of the amplified output of the Bell complement yields "
                    + "this upper bound through the padded Bell pairs."))),
                DescribeRole.Theorem))));
}
