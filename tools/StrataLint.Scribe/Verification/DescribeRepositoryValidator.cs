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
        DeclarationCatalog? declarationCatalog = null)
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

        return findings
            .OrderBy(static finding => finding.Path, StringComparer.Ordinal)
            .ThenBy(static finding => finding.Code, StringComparer.Ordinal)
            .ThenBy(static finding => finding.Message, StringComparer.Ordinal)
            .ToImmutableArray();
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
