using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class ElegantJointMeasurementInflationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/ElegantJointMeasurementInflation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact upstream inflation marginal consumers for the continuous triangle model.",
        H("Elegant joint measurement inflation identities"),
        Blocks(
            Describe.Lean(DescribeId.Create("triangle-identity"),
                DeclarationHandle.Create(Prefix + "triangle_identity_renamed"), H("Three-node triangle block"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The first three upstream nodes factor from the seven-node remainder and contribute the original p at the observed outcomes. Independent source supports are checked after arbitrary injective source-copy renaming."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("singleton-identity"),
                DeclarationHandle.Create(Prefix + "singleton_identity_renamed"), H("Singleton marginal block"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A singleton outcome factors from its eight-node remainder and contributes the two-outcome marginal sum of p. The identity is valid for arbitrary continuous response models."))), DescribeRole.Theorem))));
}
