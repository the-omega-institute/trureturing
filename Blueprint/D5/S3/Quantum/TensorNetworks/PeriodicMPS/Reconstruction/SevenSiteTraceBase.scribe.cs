using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteTraceBaseDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteTraceBase";
    private const string Title = "The zero locus and normal maps of the seven-site trace polynomial";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("sevensitetracebase-result"),
            DeclarationHandle.Create(Module + ".amplitude_first_eq_zero_iff"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("In the affine chart with first trace fixed to one, the full seven-letter trace polynomial vanishes exactly when the vacuum polynomial is zero and the second determinant and mixed trace satisfy the proportionality equations. The trace-word recurrence evaluates literal products of two bond matrices.")),
                Paragraph(Text("The same trace polynomial gives two injective normal maps. One is taken along a nonzero traceless base pencil. The other is taken along the proportional locus at a root of the vacuum polynomial."))),
            DescribeRole.Theorem))));
}
