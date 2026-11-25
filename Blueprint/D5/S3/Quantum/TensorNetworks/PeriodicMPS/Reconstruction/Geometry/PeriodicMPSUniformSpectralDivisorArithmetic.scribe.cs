using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformSpectralDivisorArithmeticDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformSpectralDivisorArithmetic";
    private const string Title = "Nonvanishing of the witness polynomial";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformspectraldivisorarithmetic-evaleval-ne-zero"),
                DeclarationHandle.Create(Module + ".evalEval_ne_zero"),
                H("Nonvanishing of the witness polynomial"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The constant term and divisibility estimates give nonvanishing throughout the required length range."))),
                DescribeRole.Theorem))));
}
