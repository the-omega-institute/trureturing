using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Scribe;

internal sealed record DescribeRedFinding(string Code, string Path, string Message);

internal static class DescribeRepositoryValidator
{
    internal static ImmutableArray<DescribeRedFinding> Validate(
        string repositoryRoot,
        IEnumerable<ScribeDocument> documents,
        LeanAxiomReport? leanReport = null,
        LibraryNoteCatalogInspection? libraryInspection = null,
        DeclarationCatalog? declarationCatalog = null,
        ProblemCandidateCatalogInspection? problemInspection = null)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(documents);
        var material = documents.ToImmutableArray();
        var generatedPaths = material
            .Select(static document => document.Header.MirrorBlueprint.Path.Value)
            .ToHashSet(StringComparer.Ordinal);
        var inspectedLibrary = libraryInspection ?? LibraryNoteCatalog.Inspect(repositoryRoot);
        var notes = inspectedLibrary.Notes
            .GroupBy(static note => note.BibKey.Value, StringComparer.Ordinal)
            .ToDictionary(
                static group => group.Key,
                static group => group.First(),
                StringComparer.Ordinal);
        var findings = ImmutableArray.CreateBuilder<DescribeRedFinding>();
        findings.AddRange(inspectedLibrary.Findings.Select(static finding =>
            new DescribeRedFinding(finding.Code, finding.Path, finding.Message)));
        var graph = DocumentGraphAssembler.Assemble(
            material,
            declarationCatalog ?? (leanReport is null ? null : DeclarationCatalog.Create(leanReport)));
        findings.AddRange(graph.Findings.Select(static finding =>
            new DescribeRedFinding(finding.Code, finding.Path, finding.Message)));

        foreach (var document in material)
        {
            ValidateGid(
                repositoryRoot,
                document.Header.Gid.Value,
                document.Header.Gid,
                generatedPaths,
                leanReport,
                findings,
                "dangling-document-gid");
            if (document.Header.MirrorEvidence is EvidenceMirror.Artifact artifact)
            {
                ValidateGid(
                    repositoryRoot,
                    document.Header.Gid.Value,
                    artifact.Reference,
                    generatedPaths,
                    leanReport,
                    findings,
                    "dangling-evidence-gid");
            }

            foreach (var anchor in document.Header.Anchors.OfType<LiteratureAnchor>())
            {
                ValidateLiteratureAnchor(
                    document.Header.Gid.Value,
                    anchor,
                    notes,
                    findings);
            }

            ValidateBlocks(
                repositoryRoot,
                document.Header.Gid.Value,
                document.Content,
                generatedPaths,
                notes,
                leanReport,
                findings);
        }

        foreach (var note in inspectedLibrary.Notes)
        {
            foreach (var reference in note.StrataTouched)
            {
                ValidateGid(
                    repositoryRoot,
                    note.RelativePath,
                    reference,
                    generatedPaths,
                    leanReport,
                    findings,
                    "dangling-library-gid");
            }

            if (note.Triage is LibraryTriage.Task task)
            {
                ValidateGid(
                    repositoryRoot,
                    note.RelativePath,
                    task.Reference,
                    generatedPaths,
                    leanReport,
                    findings,
                    "dangling-library-gid");
            }
        }

        var inspectedProblems = problemInspection ?? ProblemCandidateCatalog.Inspect(repositoryRoot);
        findings.AddRange(inspectedProblems.Findings.Select(static finding =>
            new DescribeRedFinding(finding.Code, finding.Path, finding.Message)));
        var frozenState = inspectedProblems.Candidates.IsEmpty
            ? null
            : LoadFrozenStateCatalog(repositoryRoot);
        foreach (var candidate in inspectedProblems.Candidates)
        {
            foreach (var reference in candidate.MotivationGids)
            {
                ValidateProblemMotivationGid(
                    repositoryRoot,
                    candidate.RelativePath,
                    reference,
                    generatedPaths,
                    leanReport,
                    frozenState!,
                    findings,
                    "dangling-problem-gid");
            }

            ValidateProblemSource(candidate, notes, findings);
        }

        return findings
            .OrderBy(static finding => finding.Path, StringComparer.Ordinal)
            .ThenBy(static finding => finding.Code, StringComparer.Ordinal)
            .ThenBy(static finding => finding.Message, StringComparer.Ordinal)
            .ToImmutableArray();
    }

    internal static ImmutableArray<DescribeRedFinding> ValidateIncremental(
        string repositoryRoot,
        ImmutableArray<ScribeDocument> universe,
        LeanAxiomReport? leanReport,
        LibraryNoteCatalogInspection libraryInspection,
        ProblemCandidateCatalogInspection problemInspection,
        DocumentGraph graph,
        DescribeCheckScope scope)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(libraryInspection);
        ArgumentNullException.ThrowIfNull(problemInspection);
        ArgumentNullException.ThrowIfNull(graph);
        ArgumentNullException.ThrowIfNull(scope);
        var generatedPaths = universe
            .Select(static document => document.Header.MirrorBlueprint.Path.Value)
            .ToHashSet(StringComparer.Ordinal);
        var notes = libraryInspection.Notes
            .GroupBy(static note => note.BibKey.Value, StringComparer.Ordinal)
            .ToDictionary(
                static group => group.Key,
                static group => group.First(),
                StringComparer.Ordinal);
        var findings = ImmutableArray.CreateBuilder<DescribeRedFinding>();
        if (scope.IncludeLibraryCatalogFindings)
        {
            findings.AddRange(libraryInspection.Findings.Select(static finding =>
                new DescribeRedFinding(finding.Code, finding.Path, finding.Message)));
        }
        findings.AddRange(graph.Findings
            .Where(finding => scope.DocumentGids.Contains(finding.Path))
            .Select(static finding =>
                new DescribeRedFinding(finding.Code, finding.Path, finding.Message)));

        foreach (var document in scope.Documents)
        {
            ValidateGid(
                repositoryRoot,
                document.Header.Gid.Value,
                document.Header.Gid,
                generatedPaths,
                leanReport,
                findings,
                "dangling-document-gid");
            if (document.Header.MirrorEvidence is EvidenceMirror.Artifact artifact)
            {
                ValidateGid(
                    repositoryRoot,
                    document.Header.Gid.Value,
                    artifact.Reference,
                    generatedPaths,
                    leanReport,
                    findings,
                    "dangling-evidence-gid");
            }

            foreach (var anchor in document.Header.Anchors.OfType<LiteratureAnchor>())
            {
                ValidateLiteratureAnchor(
                    document.Header.Gid.Value,
                    anchor,
                    notes,
                    findings);
            }

            ValidateBlocks(
                repositoryRoot,
                document.Header.Gid.Value,
                document.Content,
                generatedPaths,
                notes,
                leanReport,
                findings);
        }

        foreach (var note in libraryInspection.Notes
                     .Where(note => scope.LibraryPaths.Contains(note.RelativePath)))
        {
            foreach (var reference in note.StrataTouched)
            {
                ValidateGid(
                    repositoryRoot,
                    note.RelativePath,
                    reference,
                    generatedPaths,
                    leanReport,
                    findings,
                    "dangling-library-gid");
            }

            if (note.Triage is LibraryTriage.Task task)
            {
                ValidateGid(
                    repositoryRoot,
                    note.RelativePath,
                    task.Reference,
                    generatedPaths,
                    leanReport,
                    findings,
                    "dangling-library-gid");
            }
        }

        if (scope.IncludeProblemCatalogFindings)
        {
            findings.AddRange(problemInspection.Findings.Select(static finding =>
                new DescribeRedFinding(finding.Code, finding.Path, finding.Message)));
        }
        var candidates = problemInspection.Candidates
            .Where(candidate => scope.ProblemPaths.Contains(candidate.RelativePath))
            .ToImmutableArray();
        var frozenState = candidates.IsEmpty && scope.FrozenStatePaths.IsEmpty
            ? null
            : scope.IsFull
                ? LoadFrozenStateCatalog(repositoryRoot)
                : LoadFrozenStateCatalog(repositoryRoot, candidates, scope.FrozenStatePaths);
        foreach (var candidate in candidates)
        {
            foreach (var reference in candidate.MotivationGids)
            {
                ValidateProblemMotivationGid(
                    repositoryRoot,
                    candidate.RelativePath,
                    reference,
                    generatedPaths,
                    leanReport,
                    frozenState!,
                    findings,
                    "dangling-problem-gid");
            }

            ValidateProblemSource(candidate, notes, findings);
        }

        return findings
            .OrderBy(static finding => finding.Path, StringComparer.Ordinal)
            .ThenBy(static finding => finding.Code, StringComparer.Ordinal)
            .ThenBy(static finding => finding.Message, StringComparer.Ordinal)
            .ToImmutableArray();
    }

    private static FrozenStateCatalog LoadFrozenStateCatalog(string repositoryRoot)
    {
        var stateRoot = new DirectoryInfo(Path.Combine(
            repositoryRoot,
            "Golden",
            "Frozen",
            "state"));
        var entries = stateRoot.Exists
            ? stateRoot.EnumerateFiles("*.json", SearchOption.AllDirectories)
                .OrderBy(static file => file.FullName, StringComparer.Ordinal)
                .Select(file =>
                {
                    using var stream = file.OpenRead();
                    if (stream.Length > int.MaxValue)
                    {
                        throw new FormatException($"Frozen state file is too large: {file.FullName}");
                    }

                    var bytes = new byte[(int)stream.Length];
                    stream.ReadExactly(bytes);
                    var relativePath = Path.GetRelativePath(repositoryRoot, file.FullName)
                        .Replace(Path.DirectorySeparatorChar, '/');
                    return new RawRepositoryEntry(relativePath, ImmutableArray.CreateRange(bytes));
                })
            : [];
        var snapshot = SnapshotDecoder.Decode(RawRepositorySnapshot.Create(entries)) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new FormatException(failure.Message),
        };
        return FrozenStateCatalog.Load(snapshot);
    }

    private static FrozenStateCatalog LoadFrozenStateCatalog(
        string repositoryRoot,
        IEnumerable<ProblemCandidate> candidates,
        IEnumerable<string> changedStatePaths)
    {
        var entries = candidates
            .SelectMany(static candidate => candidate.MotivationGids)
            .Where(static reference => reference.IsFormalDeclaration || reference.IsFormalModule)
            .Select(static reference => reference.Path.Value)
            .Distinct(StringComparer.Ordinal)
            .Select(modulePath => "Golden/Frozen/state/" + modulePath + ".json")
            .Concat(changedStatePaths)
            .Distinct(StringComparer.Ordinal)
            .Select(relativePath => (relativePath, fullPath: Path.Combine(repositoryRoot, relativePath)))
            .Where(static item => File.Exists(item.fullPath))
            .OrderBy(static item => item.relativePath, StringComparer.Ordinal)
            .Select(static item => new RawRepositoryEntry(
                item.relativePath,
                ImmutableArray.CreateRange(File.ReadAllBytes(item.fullPath))));
        var snapshot = SnapshotDecoder.Decode(RawRepositorySnapshot.Create(entries)) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new FormatException(failure.Message),
        };
        return FrozenStateCatalog.Load(snapshot);
    }

    private static void ValidateProblemMotivationGid(
        string repositoryRoot,
        string source,
        GidRef reference,
        IReadOnlySet<string> generatedPaths,
        LeanAxiomReport? leanReport,
        FrozenStateCatalog frozenState,
        ImmutableArray<DescribeRedFinding>.Builder findings,
        string code)
    {
        if (!reference.IsFormalDeclaration && !reference.IsFormalModule)
        {
            findings.Add(new DescribeRedFinding(
                code,
                source,
                $"motivation GID must select the Formal plane: {reference.Value}"));
            return;
        }

        if (!frozenState.Records.ContainsKey(reference.Path))
        {
            findings.Add(new DescribeRedFinding(
                code,
                source,
                $"motivation GID host selector {reference.Path.Value} is not a frozen state member: "
                + reference.Value));
            return;
        }

        ValidateGid(
            repositoryRoot,
            source,
            reference,
            generatedPaths,
            leanReport,
            findings,
            code);
    }

    /// <summary>
    /// Binds a problem candidate to its literature note. The note owns the paper's
    /// identity, so the candidate's <c>arxiv_id</c> is not a second source of truth:
    /// it must reproduce the arXiv DOI the note already carries, and a candidate
    /// whose bibkey names no note is a dangling reference rather than a stylistic slip.
    /// </summary>
    private static void ValidateProblemSource(
        ProblemCandidate candidate,
        IReadOnlyDictionary<string, LibraryNote> notes,
        ImmutableArray<DescribeRedFinding>.Builder findings)
    {
        if (!notes.TryGetValue(candidate.BibKey.Value, out var note))
        {
            findings.Add(new DescribeRedFinding(
                "dangling-problem-bibkey",
                candidate.RelativePath,
                $"bibkey does not resolve to a Library note: {candidate.BibKey.Value}"));
            return;
        }

        var expected = "10.48550/arXiv." + candidate.ArxivId;
        if (note.Doi is null
            || !string.Equals(note.Doi.Value, expected, StringComparison.OrdinalIgnoreCase))
        {
            findings.Add(new DescribeRedFinding(
                "problem-source-mismatch",
                candidate.RelativePath,
                $"arxiv_id {candidate.ArxivId} expects DOI {expected} in "
                + $"{note.RelativePath}, which carries {note.Doi?.Value ?? "no DOI"}"));
        }
    }

    private static void ValidateBlocks(
        string repositoryRoot,
        string documentGid,
        BlockSequence blocks,
        IReadOnlySet<string> generatedPaths,
        IReadOnlyDictionary<string, LibraryNote> notes,
        LeanAxiomReport? leanReport,
        ImmutableArray<DescribeRedFinding>.Builder findings)
    {
        foreach (var block in blocks.Items)
        {
            switch (block)
            {
                case DocumentBlock.Paragraph paragraph:
                    foreach (var reference in paragraph.Content.Items
                                 .OfType<Inline.GidReference>()
                                 .Select(static inline => inline.Reference)
                                 .Where(static reference =>
                                     !reference.IsFormalDeclaration && !reference.IsFormalModule))
                    {
                        ValidateGid(
                            repositoryRoot,
                            documentGid,
                            reference,
                            generatedPaths,
                            leanReport,
                            findings);
                    }
                    break;
                case DocumentBlock.Section section:
                    ValidateBlocks(
                        repositoryRoot,
                        documentGid,
                        section.Content,
                        generatedPaths,
                        notes,
                        leanReport,
                        findings);
                    break;
                case DocumentBlock.Describe describe:
                    if (describe.LiteratureReference is { } literature)
                    {
                        ValidateLiterature(documentGid, literature, notes, findings);
                    }
                    foreach (var acknowledgement in describe.AcknowledgementReferences)
                    {
                        ValidateLiterature(documentGid, acknowledgement, notes, findings);
                    }
                    ValidateBlocks(
                        repositoryRoot,
                        documentGid,
                        describe.Content,
                        generatedPaths,
                        notes,
                        leanReport,
                        findings);
                    break;
            }
        }
    }

    private static void ValidateGid(
        string repositoryRoot,
        string source,
        GidRef reference,
        IReadOnlySet<string> generatedPaths,
        LeanAxiomReport? leanReport,
        ImmutableArray<DescribeRedFinding>.Builder findings,
        string code = "dangling-gid")
    {
        string? detail = null;
        if (!Exists(repositoryRoot, reference, generatedPaths))
        {
            detail = "target file is missing";
        }
        else if (leanReport is not null && reference.IsFormalDeclaration)
        {
            try
            {
                _ = LeanReferenceResolver.Resolve(
                    LeanDeclarationRef.Create(reference.Value),
                    leanReport);
            }
            catch (InvalidOperationException exception)
            {
                detail = exception.Message;
            }
        }

        if (detail is not null)
        {
            findings.Add(new DescribeRedFinding(
                code,
                source,
                $"GID does not resolve: {reference.Value} ({detail})"));
        }
    }

    private static void ValidateLiterature(
        string source,
        LibraryNoteRef reference,
        IReadOnlyDictionary<string, LibraryNote> notes,
        ImmutableArray<DescribeRedFinding>.Builder findings)
    {
        if (!notes.TryGetValue(reference.BibKey.Value, out var note)
            || !string.Equals(
                note.RelativePath,
                reference.Reference.Path.Value,
                StringComparison.Ordinal))
        {
            findings.Add(new DescribeRedFinding(
                "dangling-literature-reference",
                source,
                $"Literature reference does not resolve: {reference.Value}"));
        }
    }

    private static void ValidateLiteratureAnchor(
        string source,
        LiteratureAnchor anchor,
        IReadOnlyDictionary<string, LibraryNote> notes,
        ImmutableArray<DescribeRedFinding>.Builder findings)
    {
        if (!notes.ContainsKey(anchor.BibKey.Value))
        {
            findings.Add(new DescribeRedFinding(
                "dangling-literature-reference",
                source,
                $"Literature reference does not resolve: {anchor.CanonicalString}"));
        }
    }

    private static bool Exists(
        string repositoryRoot,
        GidRef reference,
        IReadOnlySet<string> generatedPaths) =>
        generatedPaths.Contains(reference.Path.Value)
        || File.Exists(Path.Combine(repositoryRoot, reference.Path.Value));
}
