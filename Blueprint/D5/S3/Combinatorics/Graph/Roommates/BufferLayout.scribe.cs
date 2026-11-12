using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Roommates;

internal sealed class BufferLayoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Components consumed by the exact Mertens range-two probability theorem.",
        H("BufferLayout"), Blocks(
            Paragraph(Text("Declarations without a displayed formula retain explicit statement-projection gaps. Their descriptions state the model and proof roles; they do not claim a rendered formula for an unsupported projection.")),
            Describe.Lean(DescribeId.Create("occupied-iff"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/BufferLayout.occupied_iff"),
                H("occupied_iff"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every request map into the six buffer sites that avoids the central sites 2 and 3, occupied (flags request) i is true exactly when some old request lands at i. The complete_requests proof uses this equivalence."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("occupied"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/BufferLayout.occupied"),
                H("occupied"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The deterministic layout covers every subset of the four boundary sites of a six-vertex buffer. Reserved sites stand for old requesters. The generic request-completion theorem handles any injective family of old requests avoiding the two central sites, produces an actual involution, and allows only central new singles. PaddedCompletion and CyclicClosure combine this local involution with the separate stability and global injectivity proofs."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mate"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/BufferLayout.mate"),
                H("mate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The deterministic layout covers every subset of the four boundary sites of a six-vertex buffer. Reserved sites stand for old requesters. The generic request-completion theorem handles any injective family of old requests avoiding the two central sites, produces an actual involution, and allows only central new singles. PaddedCompletion and CyclicClosure combine this local involution with the separate stability and global injectivity proofs."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("buffer-completion"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/BufferLayout.buffer_completion"),
                H("buffer_completion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The deterministic layout covers every subset of the four boundary sites of a six-vertex buffer. Reserved sites stand for old requesters. The generic request-completion theorem handles any injective family of old requests avoiding the two central sites, produces an actual involution, and allows only central new singles. PaddedCompletion and CyclicClosure combine this local involution with the separate stability and global injectivity proofs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-requests"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/BufferLayout.complete_requests"),
                H("complete_requests"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The deterministic layout covers every subset of the four boundary sites of a six-vertex buffer. Reserved sites stand for old requesters. The generic request-completion theorem handles any injective family of old requests avoiding the two central sites, produces an actual involution, and allows only central new singles. PaddedCompletion and CyclicClosure combine this local involution with the separate stability and global injectivity proofs."))), DescribeRole.Theorem))));
}
