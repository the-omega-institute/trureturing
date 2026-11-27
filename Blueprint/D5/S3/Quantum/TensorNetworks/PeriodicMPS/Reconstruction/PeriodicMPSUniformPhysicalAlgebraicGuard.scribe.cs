using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformPhysicalAlgebraicGuardDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformPhysicalAlgebraicGuard";
    private const string Title = "Exceptional slices of the physical transfer guard";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("physical-guard-zero-iff"),
                DeclarationHandle.Create(Module + ".eval_physicalGuard_eq_zero_iff"),
                H("The two exceptional slices"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the real aligned slice with k > 0, the physical transfer guard vanishes precisely when d = 0 or d = −conj(e). Here d = x₀ + i x₃ and e = x₂ + i x₄."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("physical-guard-zero-dimension"),
                DeclarationHandle.Create(Module + ".dimH_physicalGuard_zero_le"),
                H("Dimension in the nonzero mixed-trace sector"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The guard-zero locus with nonzero aligned mixed trace has real Hausdorff dimension at most six in ordinary trace-one parameters. Each slice uses three real coordinates. The physical charts add three real rotation coordinates and use two stereographic phase frames."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("physical-aligned-zero-mixed-dimension"),
                DeclarationHandle.Create(Module + ".dimH_zeroMixed_parameters_le"),
                H("Dimension of zero aligned mixed trace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The zero aligned mixed-trace sector has real Hausdorff dimension at most six in ordinary trace-one parameters. Its differentiable parametrization uses three complex coordinates."))),
                DescribeRole.Theorem))));
}
