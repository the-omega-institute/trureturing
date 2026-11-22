using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformHermiteLiteralJetDocument : IScribeDocumentDefinition
{
    private const string Title = "Literal Hermite jets of the transfer power";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhermiteliteraljet-hermite-eq-modbymonic"),
                DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformHermiteLiteralJet.hermite_eq_modByMonic"),
                H("The interpolant is the monic remainder"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Agreement of values and first derivatives implies divisibility by the squared nodal polynomial. The Hermite degree bound then gives uniqueness of the remainder."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformhermiteliteraljet-four-weight-literal-hermite-jet"),
                DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformHermiteLiteralJet.four_weight_literal_hermite_jet"),
                H("The exact four-weight matrix jet"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The characteristic polynomial of the base matrix evaluates into the square-zero ideal on an arbitrary dual-number lift. The degree-seven Hermite interpolant therefore gives the literal power, including its first-order component."))),
                DescribeRole.Theorem))));
}
