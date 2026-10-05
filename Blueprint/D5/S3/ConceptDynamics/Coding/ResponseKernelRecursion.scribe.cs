using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResponseKernelRecursionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The response relation of numbered incoming lifts has an exact successor recursion.",
        H("Response kernel successor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("response-successor-iff"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ResponseKernelRecursion.response_successor_iff"),
                H("Incoming edge lifts determine the successor response"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("An incoming lift assigns each numbered base edge a map from its terminal state fiber to its initial state fiber. Its depth response records the projected state and the initial lifted state for every path of that length. Two states have the same successor response exactly when their projections agree and their lifts along every numbered incoming edge have the same preceding response.")),
                    Paragraph(Text("The forward implication follows by appending an incoming edge to each preceding path. For the converse, every path of positive length decomposes into a prefix and its last numbered edge. Equality of the preceding responses supplies equality after lifting the prefix, and the composition law for path lifts recovers equality along the whole path. Empty prefixes, parallel edge identities and arbitrary state sets are included."))),
                DescribeRole.Theorem))));
}
