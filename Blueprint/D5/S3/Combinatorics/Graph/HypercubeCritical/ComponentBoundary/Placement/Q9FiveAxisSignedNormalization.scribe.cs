using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9FiveAxisSignedNormalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed covariance transports the Huang switching vector. The character given by the odd-indexed coordinates converts the sign convention to the parity of the preceding occupied bits.",
        H("Transport of the switching function"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-normalized-signing"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisSignedNormalization.exists_normalized_signing"),
                H("Transport of the switching function"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Signed covariance transports the Huang switching vector. The character given by the odd-indexed coordinates converts the sign convention to the parity of the preceding occupied bits."))),
                DescribeRole.Theorem)),
        []));
}
