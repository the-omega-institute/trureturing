using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class CompleteSubdivisionResolutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution.";

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/farhan2026multiset");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Once-subdivided complete graphs have no edge multiset resolving set",
        H("Once-subdivided complete graphs have no edge multiset resolving set"),
        Blocks(
            Paragraph(Text("Problem 24 of the cited versioned source, printed page 27, asks whether the edge multiset dimension of the once-subdivision of K_n is infinite for every n at least 3. Normalize a hypothetical resolving selection matrix by full complement and row rank. For n=2m use incidences e(m-1,m+1), e(m,m-1); for n=2m+1 use e(m,m+1), e(m+1,m-1). Their four counts agree. The odd case includes n=3. Rank renaming is a proved permutation; every edge and distance remains in the actual graph. The final theorem quantifies arbitrary sets of the entire vertex type and expands the minimum-endpoint distance multisets. Infinity is represented in extended naturals, with the empty family of resolving sets having infimum top. Elementary counting, matrix symmetry, finite permutations and complement identities are classical ingredients; no priority claim is made.")),
            Describe.Lean(DescribeId.Create("complete-subdivision-resolution-no-resolving-set"),
                DeclarationHandle.Create(Prefix + "no_resolving_set"),
                H("no resolving set"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every n at least three, every finite landmark subset of the full graph vertex set fails to resolve its actual edges."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-resolution-actual-edge-collision"),
                DeclarationHandle.Create(Prefix + "actual_edge_collision"),
                H("actual edge collision"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every such landmark subset there are two distinct actual unordered graph edges with equal minimum-shortest-endpoint distance multisets."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-resolution-edge-multiset-dimension"),
                DeclarationHandle.Create(Prefix + "edgeMultisetDimension"),
                H("edgeMultisetDimension"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The edge multiset dimension is the extended-natural infimum of cardinalities of resolving landmark sets. If no such set exists the infimum is infinity."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-subdivision-resolution-edge-multiset-dimension-eq-top"),
                DeclarationHandle.Create(Prefix + "edgeMultisetDimension_eq_top"),
                H("edgeMultisetDimension eq top"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every n at least three the edge multiset dimension is infinity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-resolution-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("result"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every n at least three and every arbitrary set of full graph vertices, two distinct actual edges have equal multisets of the displayed minimum actual shortest endpoint distances, and the edge multiset dimension is infinity."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("farhan-2026-complete-subdivision-edge-multiset"), ResolutionKind.Proved)))));
}
