using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Roommates;

internal sealed class BufferLayoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stable partial matchings and the Mertens range-two probability estimate.",
        H("BufferLayout"), Blocks(
            Describe.Lean(DescribeId.Create("occupied-iff"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/BufferLayout.occupied_iff"),
                H("occupied_iff"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every request map into the six buffer sites that avoids the central sites 2 and 3, occupied (flags request) i is true exactly when some old request lands at i. The complete_requests proof uses this equivalence."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("occupied"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/BufferLayout.occupied"),
                H("occupied"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite clique with a distinguished vertex, a matching covers the whole clique when its size is even and the clique without that vertex when its size is odd. The free sites in each three-site half form such a clique containing its central vertex. Mathlib's finite-clique matching theorem pairs either the whole free clique or its center-deleted subset, according to parity. The two centers are paired when both are left single. The resulting involution fixes reserved sites, uses edges of length at most two, and leaves at most one central single. PaddedCompletion and CyclicClosure use these properties for their stable matching constructions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mate"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/BufferLayout.mate"),
                H("mate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite clique with a distinguished vertex, a matching covers the whole clique when its size is even and the clique without that vertex when its size is odd. The free sites in each three-site half form such a clique containing its central vertex. Mathlib's finite-clique matching theorem pairs either the whole free clique or its center-deleted subset, according to parity. The two centers are paired when both are left single. The resulting involution fixes reserved sites, uses edges of length at most two, and leaves at most one central single. PaddedCompletion and CyclicClosure use these properties for their stable matching constructions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("buffer-completion"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/BufferLayout.buffer_completion"),
                H("buffer_completion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite clique with a distinguished vertex, a matching covers the whole clique when its size is even and the clique without that vertex when its size is odd. The free sites in each three-site half form such a clique containing its central vertex. Mathlib's finite-clique matching theorem pairs either the whole free clique or its center-deleted subset, according to parity. The two centers are paired when both are left single. The resulting involution fixes reserved sites, uses edges of length at most two, and leaves at most one central single. PaddedCompletion and CyclicClosure use these properties for their stable matching constructions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-requests"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/BufferLayout.complete_requests"),
                H("complete_requests"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite clique with a distinguished vertex, a matching covers the whole clique when its size is even and the clique without that vertex when its size is odd. The free sites in each three-site half form such a clique containing its central vertex. Mathlib's finite-clique matching theorem pairs either the whole free clique or its center-deleted subset, according to parity. The two centers are paired when both are left single. The resulting involution fixes reserved sites, uses edges of length at most two, and leaves at most one central single. PaddedCompletion and CyclicClosure use these properties for their stable matching constructions."))), DescribeRole.Theorem))));
}
