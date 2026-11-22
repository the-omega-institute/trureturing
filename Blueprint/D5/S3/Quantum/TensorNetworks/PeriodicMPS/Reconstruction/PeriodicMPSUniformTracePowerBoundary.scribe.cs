using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformTracePowerBoundaryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformTracePowerBoundary";
    private const string Title = "Odd power traces through traceless matrix pencils";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsuniformtracepowerboundary-result"),
            DeclarationHandle.Create(Module + ".trace_pow_odd_at_traceless_curve"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For an odd n and a two-by-two polynomial matrix whose trace is zero at the parameter origin, the n-th power trace is zero there. Its parameter derivative is n times the derivative of the trace, multiplied by the negative determinant at the origin raised to (n − 1)/2."))),
            DescribeRole.Theorem))));
}
