using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class RealLengthRescalingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthRescaling.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact rescaling passes from real interval lengths to their natural floors.",
        H("Real length rescaling"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("moment-rescale"),
                DeclarationHandle.Create(Prefix + "moment_rescale"),
                H("Exact mixed-moment rescaling"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive N, H and K with positive log N, rescaling every endpoint by H/K leaves the physical increments unchanged. The normalized moment acquires the factor (K/H)^(k/2)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("w4-rescale"),
                DeclarationHandle.Create(Prefix + "w4_rescale"),
                H("Scaling overlap pairings"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiplication of all endpoints by a nonnegative real r multiplies each overlap length by r and the sum of paired overlap products by r squared."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rescaled-admissible"),
                DeclarationHandle.Create(Prefix + "rescaled_admissible"),
                H("Rescaled endpoint window"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An admissible family in the window M remains admissible in the window 2M after multiplication of its endpoints by a factor between zero and two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("floor-range"),
                DeclarationHandle.Create(Prefix + "floor_range"),
                H("Floor length in the polynomial band"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<alpha<beta<1 and sufficiently large N, every H between N^alpha and N^beta has positive natural floor K, with N^(alpha/2)<=K<=N^beta and 1<=H/K<=2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("floor-variance-rate"),
                DeclarationHandle.Create(Prefix + "floor_variance_rate"),
                H("Uniform floor variance error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<alpha<beta<1, the difference between the squared logarithmic variance ratios at H and its natural floor tends uniformly to zero over N^alpha<=H<=N^beta."))),
                DescribeRole.Theorem))));
}
