using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformTraceBaseDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformTraceBase";
    private const string Title = "The trace-word zero locus in trace-one coordinates";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsuniformtracebase-result"),
            DeclarationHandle.Create(Module + ".amplitude_first_eq_zero_iff"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("At each length n ≥ 2, the full word tensor at coordinates (1, s, d, e, k) vanishes exactly when d is a root of the trace-one power polynomial, e = d s², and k = (1 − 2d)s."))),
            DescribeRole.Theorem))));
}
