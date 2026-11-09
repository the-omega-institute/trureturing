using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class ContinuousSamplingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousSampling.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous sampling transfers short interval moments from integer cells to real points.",
        H("Continuous sampling"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sampling-pointwise"),
                DeclarationHandle.Create(Prefix + "sampling_pointwise"),
                H("Pointwise cell discrepancy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an admissible interval inside a fixed window, with integer scale H and M H at most N, the centered Chebyshev increment at x differs from the centered integer-cell sum at floor x by at most 2 log(4N)+2. The two logarithmic terms account for the possible crossings at the left and right endpoints, while the additive constant accounts for the lattice centering count."))),
                DescribeRole.Theorem))));
}
