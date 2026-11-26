using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteReadoutDerivativeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteReadoutDerivative";
    private const string Title = "Normalized readout rank and the radial column";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("sevensitereadoutderivative-result"),
            DeclarationHandle.Create(Module + ".injective_fderiv_normalized_iff"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let a differentiable scalar norm coordinate be nonzero at the point and let the raw Pauli readout also be differentiable there. The derivative of the readout divided by the norm is injective exactly when the joint derivative of the norm and raw readout, augmented by the raw value in an extra radial direction, is injective.")),
                Paragraph(Text("For seven sites in the trace-one, trace-zero chart, specializing the two polynomial blocks to conjugate actual invariants produces the real trace of the raw marginal followed by its nine Pauli readings."))),
            DescribeRole.Theorem))));
}
