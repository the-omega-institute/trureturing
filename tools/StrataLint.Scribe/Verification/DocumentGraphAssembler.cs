using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Scribe;

internal sealed record DocumentGraphFinding(string Code, string Path, string Message);

public sealed class DocumentGraph
{
    internal DocumentGraph(
        ImmutableDictionary<string, ImmutableArray<DocumentEdge>> edges,
        ImmutableDictionary<string, ImmutableArray<DocumentEdge>> explicitEdges,
        ImmutableArray<DocumentGraphFinding> findings)
    {
        Edges = edges;
        ExplicitEdges = explicitEdges;
        Findings = findings;
    }

    internal ImmutableDictionary<string, ImmutableArray<DocumentEdge>> Edges { get; }

    internal ImmutableDictionary<string, ImmutableArray<DocumentEdge>> ExplicitEdges { get; }

    internal ImmutableArray<DocumentGraphFinding> Findings { get; }

    internal ImmutableArray<DocumentEdge> For(ScribeDocument document) =>
        Edges.TryGetValue(document.Header.Gid.Value, out var edges) ? edges : [];

    internal ImmutableHashSet<string> ReferencedDescribeIds(ScribeDocument document) =>
        ExplicitEdges.Values
            .SelectMany(static edges => edges)
            .OfType<DocumentEdge.NarrativeReference>()
            .Select(static edge => edge.Target)
            .OfType<NarrativeTarget.Describe>()
            .Where(target => string.Equals(
                target.DocumentGid.Value,
                document.Header.Gid.Value,
                StringComparison.Ordinal))
            .Select(static target => target.DescribeId.Value)
            .ToImmutableHashSet(StringComparer.Ordinal);
}

public static class DocumentGraphAssembler
{
    public static DocumentGraph Assemble(
        IEnumerable<ScribeDocument> documents,
        DeclarationCatalog? catalog)
    {
        ArgumentNullException.ThrowIfNull(documents);
        var material = documents.ToImmutableArray();
        var byGid = material.ToDictionary(
            static document => document.Header.Gid.Value,
            StringComparer.Ordinal);
        var byLeanModule = material.ToDictionary(
            static document => LeanModuleName(document.Header.Gid.Value),
            static document => document.Header.Gid.Value,
            StringComparer.Ordinal);
        var findings = ImmutableArray.CreateBuilder<DocumentGraphFinding>();
        var edges = ImmutableDictionary.CreateBuilder<string, ImmutableArray<DocumentEdge>>(
            StringComparer.Ordinal);
        var explicitEdges = ImmutableDictionary.CreateBuilder<string, ImmutableArray<DocumentEdge>>(
            StringComparer.Ordinal);

        foreach (var document in material.OrderBy(static item => item.Header.Gid.Value, StringComparer.Ordinal))
        {
            var assembled = Extract(document)
                .Concat(ProjectLeanImports(document, catalog, byLeanModule))
                .DistinctBy(CanonicalKey, StringComparer.Ordinal)
                .OrderBy(RoleOrder)
                .ThenBy(CanonicalKey, StringComparer.Ordinal)
                .ToImmutableArray();
            edges.Add(document.Header.Gid.Value, assembled);
            explicitEdges.Add(document.Header.Gid.Value, document.Edges);
            foreach (var edge in assembled)
            {
                var isExplicit = document.Edges.Any(candidate => string.Equals(
                    CanonicalKey(candidate), CanonicalKey(edge), StringComparison.Ordinal));
                ValidateTarget(
                    document.Header.Gid.Value,
                    edge,
                    isExplicit,
                    byGid,
                    catalog,
                    findings);
            }
        }

        FindDependencyCycles(edges, findings);
        return new DocumentGraph(
            edges.ToImmutable(),
            explicitEdges.ToImmutable(),
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
        // The canonical key is BOTH the dedup key and the ordering key (see .DistinctBy/.ThenBy
        // in Assemble). DescribeId must therefore come AFTER the declaration: putting it first
        // reorders anchors across declarations, which rewrites every emitted References section
        // and invalidates the digestion coverage GIDs that point at them. Keeping the explicit
        // anchor's key byte-identical preserves the previous ordering exactly, while the
        // "#<describe-id>" suffix still keeps two Describes on one declaration distinct.
        DocumentEdge.TruthAnchor truth => truth.DescribeId is null
            ? $"truth:{truth.Target.Value}"
            : $"truth:{truth.Target.Value}#{truth.DescribeId.Value}",
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
            .Where(edge => !IsSelfNarrativeReference(document, edge))
            .DistinctBy(CanonicalKey, StringComparer.Ordinal)
            .OrderBy(RoleOrder)
            .ThenBy(CanonicalKey, StringComparer.Ordinal)
            .ToImmutableArray();
    }

    private static IEnumerable<DocumentEdge> ProjectLeanImports(
        ScribeDocument document,
        DeclarationCatalog? catalog,
        IReadOnlyDictionary<string, string> documentsByLeanModule)
    {
        if (!RepoPath.TryCreate(document.Header.Gid.Value + ".lean", out var sourcePath))
        {
            yield break;
        }

        if (catalog is null)
        {
            yield break;
        }

        foreach (var importedModule in catalog.ImportsFor(sourcePath)
                     .Distinct(StringComparer.Ordinal)
                     .Order(StringComparer.Ordinal))
        {
            if (documentsByLeanModule.TryGetValue(importedModule, out var targetGid)
                && !string.Equals(targetGid, document.Header.Gid.Value, StringComparison.Ordinal))
            {
                yield return DocumentEdge.Dependency.Create(GidRef.Create(targetGid));
            }
        }
    }

    private static string LeanModuleName(string documentGid) =>
        documentGid.Replace('/', '.');

    private static bool IsSelfNarrativeReference(ScribeDocument document, DocumentEdge edge) =>
        edge is DocumentEdge.NarrativeReference { Target: NarrativeTarget.Document target }
        && string.Equals(
            target.DocumentGid.Value,
            document.Header.Gid.Value,
            StringComparison.Ordinal);

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
                        yield return DocumentEdge.TruthAnchor.FromDescribe(lean.Value, describe.Id);
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
        DeclarationCatalog? catalog,
        ImmutableArray<DocumentGraphFinding>.Builder findings)
    {
        if (edge is DocumentEdge.TruthAnchor truth)
        {
            if (catalog is null)
            {
                return;
            }
            try
            {
                _ = catalog.Resolve(DeclarationHandle.Create(truth.Target.Value));
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
