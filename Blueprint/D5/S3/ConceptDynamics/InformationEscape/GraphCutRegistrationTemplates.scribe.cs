using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class GraphCutRegistrationTemplatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A dependent signature types the full binary edge-gradient readout on arbitrary simple graphs.",
        H("GraphCutRegistrationTemplates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("graph-gradient-signature"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/InformationEscape/GraphCutRegistrationTemplates.graphGradientSignature"),
                H("Binary graph-gradient signature"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Parameters pair an arbitrary vertex type V with a SimpleGraph V. States are all "
                        + "binary vertex labelings V -> ZMod 2. The sole role is Unit, and its output "
                        + "is a binary word on the full edge set G.edgeSet; the anchor type is Empty. "
                        + "The signature imposes no finiteness condition on vertices or edges. The "
                        + "edge-connectivity consumer supplies Fintype G.edgeSet when it measures the "
                        + "Hamming weight of an edge gradient. Reg/D5/S3/Fourier/CharacterSelection/"
                        + "EdgeConnectivityGradientWeight uses this signature with edgeDifferential "
                        + "as the actual full-edge readout. The definition is an operand for that "
                        + "source-bound registration, not a theorem or a registration proof."))),
                DescribeRole.Definition))));
}
