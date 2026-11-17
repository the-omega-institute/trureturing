using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SymmetricTwentyTwoNonEmbeddingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric Twenty Two Non Embedding", H("Symmetric Twenty Two Non Embedding"),
        Blocks(
            Paragraph(Text("Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, section 7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2), ask whether f2(Q9) is three or four. The external problem and its published results belong to that paper. This repository proof addresses a local structural branch; no solution of the original 258-point problem or literature priority is claimed. The original problem remains unresolved.")),
            Paragraph(Text("The explicit twenty-two-vertex, twenty-nine-edge candidate has no induced embedding in a finite Boolean cube of any dimension. Each coordinate cut obeys short-path constraints; a kernel-checked parity consequence contradicts the three distinguished edges. The statement concerns this explicit candidate, not all symmetric slices until the actual-classification bridges are applied.")),
            Describe.Lean(
                DescribeId.Create("symmetric-twenty-two-non-embedding-claim"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyTwoNonEmbedding.claim"),
                H("claim"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There exist n and an injective vertex map from the explicit twenty-two-vertex graph into the n-dimensional Boolean cube that preserves and reflects adjacency."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("symmetric-twenty-two-non-embedding-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyTwoNonEmbedding.result"),
                H("result"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The theorem has literally type Not claim, excluding this explicit candidate in every finite cube dimension by coordinate-cut parity."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceNonEmbedding"))
        ]));
}
