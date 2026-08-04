using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Scribe;

internal sealed record DocumentGraphFinding(string Code, string Path, string Message);

public sealed class DocumentGraph
{
    internal DocumentGraph(
        ImmutableDictionary<string, ImmutableArray<DocumentEdge>> edges,
        ImmutableArray<DocumentGraphFinding> findings)
    {
        Edges = edges;
        Findings = findings;
    }

    internal ImmutableDictionary<string, ImmutableArray<DocumentEdge>> Edges { get; }

    internal ImmutableArray<DocumentGraphFinding> Findings { get; }

    internal ImmutableArray<DocumentEdge> For(ScribeDocument document) =>
        Edges.TryGetValue(document.Header.Gid.Value, out var edges) ? edges : [];
}

public static class DocumentGraphAssembler
{
    public static DocumentGraph Assemble(
        IEnumerable<ScribeDocument> documents,
        LeanAxiomReport? leanReport)
    {
        ArgumentNullException.ThrowIfNull(documents);
        var material = documents.ToImmutableArray();
        var byGid = material.ToDictionary(
            static document => document.Header.Gid.Value,
            StringComparer.Ordinal);
        var findings = ImmutableArray.CreateBuilder<DocumentGraphFinding>();
        var edges = ImmutableDictionary.CreateBuilder<string, ImmutableArray<DocumentEdge>>(
            StringComparer.Ordinal);

        foreach (var document in material.OrderBy(static item => item.Header.Gid.Value, StringComparer.Ordinal))
        {
            var assembled = Extract(document);
            edges.Add(document.Header.Gid.Value, assembled);
            foreach (var edge in assembled)
            {
                var isExplicit = document.Edges.Any(candidate => string.Equals(
                    CanonicalKey(candidate), CanonicalKey(edge), StringComparison.Ordinal));
                ValidateTarget(
                    document.Header.Gid.Value,
                    edge,
                    isExplicit,
                    byGid,
                    leanReport,
                    findings);
            }
        }

        FindDependencyCycles(edges, findings);
        return new DocumentGraph(
            edges.ToImmutable(),
            findings
                .OrderBy(static finding => finding.Path, StringComparer.Ordinal)
                .ThenBy(static finding => finding.Code, StringComparer.Ordinal)
                .ThenBy(static finding => finding.Message, StringComparer.Ordinal)
                .ToImmutableArray());
    }

    internal static int RoleOrder(DocumentEdge edge) => edge switch
    {
        DocumentEdge.TruthAnchor => 0,
        DocumentEdge.Dependency => 1,
        DocumentEdge.NarrativeReference => 2,
        _ => throw new InvalidOperationException("Unknown document edge."),
    };

    internal static string CanonicalKey(DocumentEdge edge) => edge switch
    {
        DocumentEdge.TruthAnchor truth => $"truth:{truth.Target.Value}",
        DocumentEdge.Dependency dependency => $"dependency:{dependency.Target.Value}",
        DocumentEdge.NarrativeReference { Target: NarrativeTarget.Document document } =>
            $"narrative:{document.DocumentGid.Value}",
        DocumentEdge.NarrativeReference { Target: NarrativeTarget.Describe describe } =>
            $"narrative:{describe.DocumentGid.Value}#describe/{describe.DescribeId.Value}",
        _ => throw new InvalidOperationException("Unknown document edge."),
    };

    internal static ImmutableArray<DocumentEdge> Extract(ScribeDocument document)
    {
        ArgumentNullException.ThrowIfNull(document);
        return document.Edges
            .Concat(ImplicitEdges(document.Content))
            .DistinctBy(CanonicalKey, StringComparer.Ordinal)
            .OrderBy(RoleOrder)
            .ThenBy(CanonicalKey, StringComparer.Ordinal)
            .ToImmutableArray();
    }

    private static IEnumerable<DocumentEdge> ImplicitEdges(BlockSequence blocks)
    {
        foreach (var block in blocks.Items)
        {
            switch (block)
            {
                case DocumentBlock.Paragraph paragraph:
                    foreach (var reference in paragraph.Content.Items.OfType<Inline.GidReference>())
                    {
                        if (reference.Reference.IsFormalDeclaration)
                        {
                            yield return DocumentEdge.TruthAnchor.Create(
                                LeanDeclarationRef.Create(reference.Reference.Value));
                        }
                        else if (reference.Reference.IsFormalModule)
                        {
                            yield return DocumentEdge.NarrativeReference.ToDocument(
                                reference.Reference);
                        }
                    }
                    break;
                case DocumentBlock.Section section:
                    foreach (var edge in ImplicitEdges(section.Content))
                    {
                        yield return edge;
                    }
                    break;
                case DocumentBlock.Describe describe:
                    if (describe.Statement is DescribeStatement.LeanDeclaration lean)
                    {
                        yield return DocumentEdge.TruthAnchor.Create(lean.Value);
                    }
                    foreach (var edge in ImplicitEdges(describe.Content))
                    {
                        yield return edge;
                    }
                    break;
            }
        }
    }

    private static void ValidateTarget(
        string source,
        DocumentEdge edge,
        bool isExplicit,
        IReadOnlyDictionary<string, ScribeDocument> documents,
        LeanAxiomReport? leanReport,
        ImmutableArray<DocumentGraphFinding>.Builder findings)
    {
        if (edge is DocumentEdge.TruthAnchor truth)
        {
            if (leanReport is null)
            {
                return;
            }
            try
            {
                _ = LeanReferenceResolver.Resolve(truth.Target, leanReport);
            }
            catch (InvalidOperationException exception)
            {
                findings.Add(new DocumentGraphFinding(
                    "dangling-gid", source,
                    $"Truth anchor does not resolve: {truth.Target.Value} ({exception.Message})"));
            }
            return;
        }

        var target = edge switch
        {
            DocumentEdge.Dependency dependency => dependency.Target,
            DocumentEdge.NarrativeReference { Target: NarrativeTarget.Document document } =>
                document.DocumentGid,
            DocumentEdge.NarrativeReference { Target: NarrativeTarget.Describe describe } =>
                describe.DocumentGid,
            _ => throw new InvalidOperationException("Unknown document edge."),
        };
        if (!documents.TryGetValue(target.Value, out var targetDocument))
        {
            findings.Add(new DocumentGraphFinding(
                isExplicit ? "dangling-document-edge" : "dangling-gid", source,
                $"Document edge does not resolve: {target.Value}"));
            return;
        }

        if (edge is DocumentEdge.NarrativeReference { Target: NarrativeTarget.Describe describeTarget }
            && !DescribeIds(targetDocument.Content).Contains(describeTarget.DescribeId.Value))
        {
            findings.Add(new DocumentGraphFinding(
                "dangling-describe-edge", source,
                $"Describe edge does not resolve: {target.Value}#describe/{describeTarget.DescribeId.Value}"));
        }
    }

    private static HashSet<string> DescribeIds(BlockSequence blocks)
    {
        var ids = new HashSet<string>(StringComparer.Ordinal);
        Visit(blocks);
        return ids;

        void Visit(BlockSequence content)
        {
            foreach (var block in content.Items)
            {
                switch (block)
                {
                    case DocumentBlock.Section section:
                        Visit(section.Content);
                        break;
                    case DocumentBlock.Describe describe:
                        ids.Add(describe.Id.Value);
                        Visit(describe.Content);
                        break;
                }
            }
        }
    }

    private static void FindDependencyCycles(
        IReadOnlyDictionary<string, ImmutableArray<DocumentEdge>> edges,
        ImmutableArray<DocumentGraphFinding>.Builder findings)
    {
        var state = new Dictionary<string, int>(StringComparer.Ordinal);
        var stack = new List<string>();
        var reported = new HashSet<string>(StringComparer.Ordinal);
        foreach (var node in edges.Keys.OrderBy(static value => value, StringComparer.Ordinal))
        {
            Visit(node);
        }
        return;

        void Visit(string node)
        {
            if (state.GetValueOrDefault(node) == 2)
            {
                return;
            }
            state[node] = 1;
            stack.Add(node);
            foreach (var target in edges[node]
                         .OfType<DocumentEdge.Dependency>()
                         .Select(static edge => edge.Target.Value)
                         .Where(edges.ContainsKey)
                         .OrderBy(static value => value, StringComparer.Ordinal))
            {
                if (state.GetValueOrDefault(target) == 0)
                {
                    Visit(target);
                }
                else if (state[target] == 1)
                {
                    var start = stack.IndexOf(target);
                    var cycle = stack.Skip(start).Append(target).ToArray();
                    var key = string.Join(" -> ", cycle);
                    if (reported.Add(key))
                    {
                        findings.Add(new DocumentGraphFinding(
                            "dependency-cycle", target, $"Dependency cycle: {key}"));
                    }
                }
            }
            stack.RemoveAt(stack.Count - 1);
            state[node] = 2;
        }
    }
}
