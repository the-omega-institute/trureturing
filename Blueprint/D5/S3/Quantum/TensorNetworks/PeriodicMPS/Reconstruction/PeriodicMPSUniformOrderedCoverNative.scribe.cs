using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformOrderedCoverNativeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformOrderedCoverNative";
    private const string Title = "Native polynomial divisor exclusion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformorderedcovernative-native-commondivisor-avoids-special"),
                DeclarationHandle.Create(Module + ".native_commonDivisor_avoids_special"),
                H("Native polynomial divisor exclusion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An irreducible common divisor of the ten native cofactors off the basic guard divides neither the zero-root equation nor the discriminant in determinant coordinates."))),
                DescribeRole.Theorem))));
}
