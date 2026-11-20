using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection;

internal sealed class PeriodicMPSUniformChiralityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reflection/PeriodicMPSUniformChirality";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform nonzero chirality witness",
        H("A uniform nonzero chirality witness"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformchirality-normalizedmarginal-chirality-negative"),
                DeclarationHandle.Create(Module + ".normalizedMarginal_chirality_negative"),
                H("A uniform nonzero chirality witness"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same Gaussian-integer core gives a strictly negative normalized chirality determinant at every ring length at least seven. The sign comes from exact recurrence and rational bounds."))),
                DescribeRole.Theorem))));
}
