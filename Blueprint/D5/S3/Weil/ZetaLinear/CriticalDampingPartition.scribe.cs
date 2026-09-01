using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaLinear;

internal sealed class CriticalDampingPartitionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaLinear/CriticalDampingPartition."
            + "critical_damping_partition_certificate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite reflection-symmetric damping spectrum has equivalent diagonal, "
            + "centered-exponential, and hyperbolic-cosine partition traces, with a "
            + "nonnegative defect that vanishes precisely on the critical line.",
        H("Critical Damping Partition"),
        Blocks(Describe.Lean(
            DescribeId.Create("critical-damping-partition-certificate"),
            DeclarationHandle.Create(Declaration),
            H("The centered damping partition has a nonnegative critical defect"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A finite family of real damping rates defines a complex diagonal "
                        + "matrix. Subtracting one half times the identity produces the "
                        + "centered damping operator, while the normalized partition "
                        + "function is the exponential prefactor times the finite heat "
                        + "sum.")),
                Paragraph(Text(
                    "The reflection hypothesis is witnessed by a permutation that negates "
                        + "every centered rate. It cancels the odd exponential contribution "
                        + "and identifies the partition with the trace of the matrix "
                        + "hyperbolic cosine.")),
                Paragraph(Text(
                    "The resulting partition defect is a finite sum of cosh(x)-1 terms and "
                        + "is nonnegative. At every nonzero scale it vanishes exactly when "
                        + "all damping rates equal one half. The same module proves the "
                        + "finite maximum norm formula and explicit critical and off-line "
                        + "three-point witnesses."))),
            DescribeRole.Theorem))));
}
