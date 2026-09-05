using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Scribe;

internal sealed class DescribeCheckScope
{
    private const string BlueprintPrefix = "Blueprint/";
    private const string BlueprintSuffix = ".scribe.cs";
    private const string FrozenPrefix = "Golden/Frozen/state/";

    private DescribeCheckScope(
        ImmutableArray<ScribeDocument> documents,
        ImmutableHashSet<string> documentGids,
        ImmutableArray<string> leanSourcePaths,
        ImmutableArray<string> blueprintSourcePaths,
        ImmutableHashSet<string> libraryPaths,
        ImmutableHashSet<string> problemPaths,
        ImmutableHashSet<string> frozenStatePaths,
        bool includeLibraryCatalogFindings,
        bool includeProblemCatalogFindings,
        bool validateCensus,
        bool fullValidation)
    {
        Documents = documents;
        DocumentGids = documentGids;
        LeanSourcePaths = leanSourcePaths;
        BlueprintSourcePaths = blueprintSourcePaths;
        LibraryPaths = libraryPaths;
        ProblemPaths = problemPaths;
        FrozenStatePaths = frozenStatePaths;
        IncludeLibraryCatalogFindings = includeLibraryCatalogFindings;
        IncludeProblemCatalogFindings = includeProblemCatalogFindings;
        ValidateCensus = validateCensus;
        IsFull = fullValidation;
    }

    internal ImmutableArray<ScribeDocument> Documents { get; }

    internal ImmutableHashSet<string> DocumentGids { get; }

    internal ImmutableArray<string> LeanSourcePaths { get; }

    internal ImmutableArray<string> BlueprintSourcePaths { get; }

    internal ImmutableHashSet<string> LibraryPaths { get; }

    internal ImmutableHashSet<string> ProblemPaths { get; }

    internal ImmutableHashSet<string> FrozenStatePaths { get; }

    internal bool IncludeLibraryCatalogFindings { get; }

    internal bool IncludeProblemCatalogFindings { get; }

    internal bool ValidateCensus { get; }

    internal bool IsFull { get; }

    internal static DescribeCheckScope Create(
        ImmutableArray<ScribeDocument> documents,
        ImmutableArray<string> changedPaths,
        DocumentGraph graph,
        LibraryNoteCatalogInspection library,
        ProblemCandidateCatalogInspection problems)
    {
        ArgumentNullException.ThrowIfNull(graph);
        ArgumentNullException.ThrowIfNull(library);
        ArgumentNullException.ThrowIfNull(problems);

        var paths = changedPaths
            .Select(NormalizePath)
            .Where(static path => path.Length > 0)
            .ToImmutableHashSet(StringComparer.Ordinal);
        var validateAll = paths.Any(IsGlobalInput);
        var changedLean = paths
            .Where(static path => path.StartsWith("D5/", StringComparison.Ordinal)
                && path.EndsWith(".lean", StringComparison.Ordinal))
            .ToImmutableHashSet(StringComparer.Ordinal);
        var changedBlueprint = paths
            .Where(static path => path.StartsWith(BlueprintPrefix, StringComparison.Ordinal)
                && path.EndsWith(BlueprintSuffix, StringComparison.Ordinal))
            .ToImmutableHashSet(StringComparer.Ordinal);
        var changedLibrary = paths
            .Where(static path => path.StartsWith("Library/", StringComparison.Ordinal)
                && path.EndsWith(".md", StringComparison.Ordinal))
            .ToImmutableHashSet(StringComparer.Ordinal);
        var changedProblems = paths
            .Where(static path => path.StartsWith("Problems/", StringComparison.Ordinal)
                && path.EndsWith(".md", StringComparison.Ordinal))
            .ToImmutableHashSet(StringComparer.Ordinal);
        var changedFrozenPaths = paths
            .Where(static path => path.StartsWith(FrozenPrefix, StringComparison.Ordinal)
                && path.EndsWith(".json", StringComparison.Ordinal))
            .ToImmutableHashSet(StringComparer.Ordinal);
        var changedFrozenModules = changedFrozenPaths
            .Where(static path => path.EndsWith(".lean.json", StringComparison.Ordinal))
            .Select(static path => path[FrozenPrefix.Length..^".json".Length])
            .ToImmutableHashSet(StringComparer.Ordinal);
        var changedGidPaths = changedLean
            .Concat(changedBlueprint.Select(static path =>
                path[..^BlueprintSuffix.Length] + ".md"))
            .ToImmutableHashSet(StringComparer.Ordinal);

        var affected = validateAll
            ? documents.Select(static document => document.Header.Gid.Value)
                .ToHashSet(StringComparer.Ordinal)
            : new HashSet<string>(StringComparer.Ordinal);
        foreach (var path in changedBlueprint)
        {
            var gid = path[BlueprintPrefix.Length..^BlueprintSuffix.Length];
            affected.Add(gid);
        }
        foreach (var path in changedLean)
        {
            affected.Add(path[..^".lean".Length]);
        }

        var changedBibKeys = changedLibrary
            .Select(static path => Path.GetFileNameWithoutExtension(path)!)
            .ToImmutableHashSet(StringComparer.Ordinal);
        foreach (var document in documents)
        {
            if (changedBlueprint.Contains(document.Header.MirrorBlueprint.Path.Value)
                || DocumentTouchesGidPath(document, changedGidPaths)
                || DocumentReferencesLibrary(document, changedBibKeys))
            {
                affected.Add(document.Header.Gid.Value);
            }
        }

        // Dependency cycles need both directions. Narrative edges only flow backwards:
        // a changed target can invalidate its callers, while a changed caller is checked itself.
        var expanded = true;
        while (expanded)
        {
            expanded = false;
            foreach (var (source, edges) in graph.Edges)
            {
                foreach (var edge in edges)
                {
                    var target = DocumentTarget(edge);
                    if (target is null) continue;
                    if (edge is DocumentEdge.Dependency
                        && (affected.Contains(source) || affected.Contains(target)))
                    {
                        expanded |= affected.Add(source);
                        expanded |= affected.Add(target);
                    }
                    else if (affected.Contains(target))
                    {
                        expanded |= affected.Add(source);
                    }
                }
            }
        }

        var affectedDocuments = documents
            .Where(document => affected.Contains(document.Header.Gid.Value))
            .OrderBy(static document => document.Header.Gid.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        var affectedLibrary = library.Notes
            .Where(note => validateAll
                || changedLibrary.Contains(note.RelativePath)
                || note.StrataTouched.Any(reference => changedGidPaths.Contains(reference.Path.Value))
                || note.Triage is LibraryTriage.Task task
                    && changedGidPaths.Contains(task.Reference.Path.Value))
            .Select(static note => note.RelativePath)
            .Concat(changedLibrary)
            .ToImmutableHashSet(StringComparer.Ordinal);
        var affectedProblems = problems.Candidates
            .Where(candidate => validateAll
                || changedProblems.Contains(candidate.RelativePath)
                || changedBibKeys.Contains(candidate.BibKey.Value)
                || candidate.MotivationGids.Any(reference =>
                    changedLean.Contains(reference.Path.Value)
                    || changedFrozenModules.Contains(reference.Path.Value)))
            .Select(static candidate => candidate.RelativePath)
            .Concat(changedProblems)
            .ToImmutableHashSet(StringComparer.Ordinal);

        var leanSources = validateAll
            ? EnumerateLeanSources(documents, graph)
            : changedLean.Order(StringComparer.Ordinal).ToImmutableArray();
        var blueprintSources = validateAll
            ? documents.Select(static document => document.Header.MirrorBlueprint.Path.Value)
                .Order(StringComparer.Ordinal)
                .ToImmutableArray()
            : changedBlueprint.Order(StringComparer.Ordinal).ToImmutableArray();
        return new DescribeCheckScope(
            affectedDocuments,
            affected.ToImmutableHashSet(StringComparer.Ordinal),
            leanSources,
            blueprintSources,
            affectedLibrary,
            affectedProblems,
            changedFrozenPaths,
            validateAll || !changedLibrary.IsEmpty,
            validateAll || !changedProblems.IsEmpty,
            validateAll
                || !changedBlueprint.IsEmpty
                || paths.Contains("Meta/BACKFILL.yaml")
                || paths.Any(static path => path.StartsWith(
                    "Meta/Digestion/backfill/", StringComparison.Ordinal)),
            validateAll);
    }

    private static ImmutableArray<string> EnumerateLeanSources(
        ImmutableArray<ScribeDocument> documents,
        DocumentGraph graph) => documents
        .Select(static document => document.Header.Gid.Path.Value)
        .Concat(graph.Edges.Values
            .SelectMany(static edges => edges)
            .OfType<DocumentEdge.TruthAnchor>()
            .Select(static edge => edge.Target.Reference.Path.Value))
        .Where(static path => path.StartsWith("D5/", StringComparison.Ordinal))
        .Distinct(StringComparer.Ordinal)
        .Order(StringComparer.Ordinal)
        .ToImmutableArray();

    private static bool DocumentTouchesGidPath(
        ScribeDocument document,
        ImmutableHashSet<string> changedPaths)
    {
        if (changedPaths.IsEmpty) return false;
        if (changedPaths.Contains(document.Header.Gid.Path.Value)
            || changedPaths.Contains(document.Header.MirrorBlueprint.Path.Value)
            || document.Header.MirrorEvidence is EvidenceMirror.Artifact artifact
                && changedPaths.Contains(artifact.Reference.Path.Value))
        {
            return true;
        }
        return DocumentGraphAssembler.Extract(document).Any(edge => edge switch
        {
            DocumentEdge.TruthAnchor truth => changedPaths.Contains(truth.Target.Reference.Path.Value),
            _ => false,
        }) || EnumerateBlocks(document.Content)
            .OfType<DocumentBlock.Paragraph>()
            .SelectMany(static paragraph => paragraph.Content.Items)
            .OfType<Inline.GidReference>()
            .Any(reference => changedPaths.Contains(reference.Reference.Path.Value));
    }

    private static bool DocumentReferencesLibrary(
        ScribeDocument document,
        ImmutableHashSet<string> bibKeys)
    {
        if (bibKeys.IsEmpty) return false;
        if (document.Header.Anchors.OfType<LiteratureAnchor>()
            .Any(anchor => bibKeys.Contains(anchor.BibKey.Value)))
        {
            return true;
        }
        return EnumerateBlocks(document.Content)
            .OfType<DocumentBlock.Describe>()
            .SelectMany(static describe => describe.LiteratureReference is { } literature
                ? describe.AcknowledgementReferences.Prepend(literature)
                : describe.AcknowledgementReferences)
            .Any(reference => bibKeys.Contains(reference.BibKey.Value));
    }

    private static IEnumerable<DocumentBlock> EnumerateBlocks(BlockSequence blocks)
    {
        foreach (var block in blocks.Items)
        {
            yield return block;
            var nested = block switch
            {
                DocumentBlock.Section section => section.Content,
                DocumentBlock.Describe describe => describe.Content,
                _ => null,
            };
            if (nested is null) continue;
            foreach (var descendant in EnumerateBlocks(nested)) yield return descendant;
        }
    }

    private static string? DocumentTarget(DocumentEdge edge) => edge switch
    {
        DocumentEdge.Dependency dependency => dependency.Target.Value,
        DocumentEdge.NarrativeReference { Target: NarrativeTarget.Document document } =>
            document.DocumentGid.Value,
        DocumentEdge.NarrativeReference { Target: NarrativeTarget.Describe describe } =>
            describe.DocumentGid.Value,
        _ => null,
    };

    private static string NormalizePath(string path) =>
        path.Replace('\\', '/').Trim();

    private static bool IsGlobalInput(string path) => path is
        "Trureturing.lean" or "lean-toolchain" or "lake-manifest.json" or
        "lakefile.toml" or "lakefile.lean" or "global.json" or
        "Directory.Build.props" or "Directory.Build.targets" or "Directory.Packages.props"
        || path.StartsWith("tools/", StringComparison.Ordinal)
            && !path.StartsWith("tools/tests/", StringComparison.Ordinal)
        || path.StartsWith(".github/", StringComparison.Ordinal);
}
