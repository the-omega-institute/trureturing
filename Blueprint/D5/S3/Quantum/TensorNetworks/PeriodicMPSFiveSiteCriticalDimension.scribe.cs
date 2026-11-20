using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFiveSiteCriticalDimensionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCriticalDimension";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Codimension of the five-site critical equations",
        H("Codimension of the five-site critical equations"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesitecriticaldimension-codimension"),
            DeclarationHandle.Create(Module + ".critical_minor_codimension"),
            H("Two independent critical equations"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "The second minor is a nonzero divisor modulo the first. The quotient by both equations has Krull dimension at most eight."))),
            DescribeRole.Theorem))));
}
