using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve;

internal sealed class SieveSmoothKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Support and mass of the smoothing kernel",
        H("Support and mass of the smoothing kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("smoothing-kernel-support"),
                DeclarationHandle.Create(Prefix + "smoothing_kernel_support"),
                H("Exact kernel support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive delta, the topological support of smoothingKernel is the closed interval [delta,3 delta], and its nonzero set is the open interval (delta,3 delta)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("smoothing-kernel-mass"),
                DeclarationHandle.Create(Prefix + "smoothing_kernel_mass"),
                H("Nonnegative unit mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive delta, smoothingKernel is nonnegative at every real point and its integral over the real line is one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("smooth-interval-support"),
                DeclarationHandle.Create(Prefix + "smooth_interval_support"),
                H("Compact shifted support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For zero at most a at most b and positive delta, the smoothed interval indicator has compact support contained in [a+delta,b+3 delta]. This includes the empty interval a=b."))),
                DescribeRole.Theorem))));
}
