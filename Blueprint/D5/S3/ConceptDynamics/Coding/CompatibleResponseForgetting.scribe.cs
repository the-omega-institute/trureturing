using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CompatibleResponseForgettingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A compatible numbered path certificate constructs an essential finite square graph with both boundaries forgetting after its lag.",
        H("Compatible response forgetting"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("incoming-response-step"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting.incoming_response_step"),
                H("Incoming lifts respect response depth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For two states with the same numbered path responses at depth d plus one, lifting the same incoming base edge places their predecessor states in one depth-d response class. Appending that edge to each depth-d path identifies the resulting lifted paths with the original depth-(d+1) observations."))),
                DescribeRole.Theorem),
            Paragraph(Text("Numbered compatible squares give incoming and outgoing lifts on the R-edge states. Their finite sweeps identify responses with the certificate path bijections, and counting edge fibers yields the first row and column response matrices.")))));
}
