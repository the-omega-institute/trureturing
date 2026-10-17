using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class CompleteSubdivisionMetricDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric.";

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/farhan2026multiset");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shortest distances in a once-subdivided complete graph",
        H("Shortest distances in a once-subdivided complete graph"),
        Blocks(
            Paragraph(Text("The graph has all n original vertices and one midpoint for every unordered pair of distinct originals. Only original-to-incident-midpoint pairs are adjacent. This is the once-subdivision of every edge of the complete graph, as defined on printed page 21 of the cited versioned source. Reachability is proved before natural-valued graph distances are used.")),
            Describe.Lean(DescribeId.Create("complete-subdivision-metric-midpoint"),
                DeclarationHandle.Create(Prefix + "Midpoint"),
                H("Midpoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Unordered pairs of distinct original vertices label exactly one inserted vertex per complete-graph edge."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-subdivision-metric-vertex"),
                DeclarationHandle.Create(Prefix + "Vertex"),
                H("Vertex"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The full finite vertex type is the disjoint union of originals and all inserted midpoints."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-subdivision-metric-graph"),
                DeclarationHandle.Create(Prefix + "graph"),
                H("graph"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Adjacency holds exactly between an original vertex and a midpoint containing it."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-subdivision-metric-subdivision-vertex"),
                DeclarationHandle.Create(Prefix + "subdivisionVertex"),
                H("subdivisionVertex"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Distinct original endpoints determine their single unordered midpoint."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-subdivision-metric-midpoint-swap"),
                DeclarationHandle.Create(Prefix + "midpoint_swap"),
                H("midpoint swap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Exchanging the original endpoints preserves their midpoint."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-metric-adj-original-midpoint"),
                DeclarationHandle.Create(Prefix + "adj_original_midpoint"),
                H("adj original midpoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Original-to-midpoint adjacency is exactly membership in the underlying unordered pair."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-metric-reachable"),
                DeclarationHandle.Create(Prefix + "reachable"),
                H("reachable"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Every pair of actual graph vertices is joined by a walk."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-metric-dist-original-original"),
                DeclarationHandle.Create(Prefix + "dist_original_original"),
                H("dist original original"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Original vertices have shortest distance zero when equal and two when distinct."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-metric-dist-original-midpoint"),
                DeclarationHandle.Create(Prefix + "dist_original_midpoint"),
                H("dist original midpoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("An original vertex has shortest distance one to an incident midpoint and three to a nonincident midpoint."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-metric-dist-midpoint-midpoint"),
                DeclarationHandle.Create(Prefix + "dist_midpoint_midpoint"),
                H("dist midpoint midpoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Midpoints have shortest distance zero when equal, two when distinct with a common endpoint, and four when disjoint."))), DescribeRole.Theorem))));
}
