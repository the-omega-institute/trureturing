using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResponseFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Numbered response decompositions give SSE steps; equal first-level row and column classes construct an explicit quotient diamond.",
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
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("first-response-diamond"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ResponseFactorization.first_response_diamond"),
                H("First response row and column diamond"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Equal-column and equal-row response classes determine a common matrix from class representatives. Their membership and representative matrices recover the original graph, while the class-intersection matrix and the common matrix give an explicit elementary strong shift equivalence between the two first quotients. The factorization is derived from the row and column properties."))),
                DescribeRole.Theorem))));
}
