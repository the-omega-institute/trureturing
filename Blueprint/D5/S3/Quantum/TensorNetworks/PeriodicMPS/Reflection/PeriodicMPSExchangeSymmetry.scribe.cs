using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection;

internal sealed class PeriodicMPSExchangeSymmetryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reflection/PeriodicMPSExchangeSymmetry";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exchange symmetry of the actual two-site state",
        H("Exchange symmetry of the actual two-site state"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsexchangesymmetry-normalizedmarginal-exchangesymmetric"),
                DeclarationHandle.Create(Module + ".normalizedMarginal_exchangeSymmetric"),
                H("Exchange symmetry of the actual two-site state"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reversal of the trace words makes the literal normalized adjacent observation exchange symmetric for every binary bond-two core."))),
                DescribeRole.Theorem))));
}
