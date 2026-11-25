using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformLiteralJetSpecializationDocument : IScribeDocumentDefinition
{
    private const string Title = "Specialization of the monic literal jet";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformliteraljetspecialization-literaljetremainder-eq-hermite"),
                DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLiteralJetSpecialization.literalJetRemainder_eq_hermite"),
                H("The split remainder equals the Hermite interpolant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At distinct nodes, explicit Hermite cardinal interpolation and monic division define the same polynomial."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformliteraljetspecialization-invariantliteraljet-map"),
                DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLiteralJetSpecialization.invariantLiteralJet_map"),
                H("Coefficient specialization commutes with the invariant remainder"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Division by the squared invariant characteristic preserves the literal jet under any coefficient ring homomorphism."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformliteraljetspecialization-invariantliteraljet-collision"),
                DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLiteralJetSpecialization.invariantLiteralJet_collision"),
                H("The invariant remainder at the fourfold collision"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At the colliding invariant values, scaling by four to the residual length gives the binomial polynomial truncated at degree seven."))),
                DescribeRole.Theorem))));
}
