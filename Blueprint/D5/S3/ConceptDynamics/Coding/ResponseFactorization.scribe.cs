using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResponseFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A numbered finite response decomposition yields the corresponding matrix product and one explicit SSE step.",
        H("Numbered response factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("numbered-response-step-is-sse"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ResponseFactorization.response_step_is_sse"),
                H("A finite response step is an SSE step"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every pair of outside vertices, the numbered edges of the original graph are put in bijection with a middle response state together with a numbered left and right edge. Counting this actual finite decomposition proves the matrix product identity. Swapping the two factors then gives the target matrix and the elementary one-step strong shift equivalence chain."))),
                DescribeRole.Theorem))));
}
