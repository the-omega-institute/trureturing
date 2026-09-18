using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Scribe;

internal static partial class DescribeRepositoryValidator
{
    // The full Describe validator and the registered Library unit share these predicates.
    // Lean declaration references keep their normal report-backed resolution.
    internal static ImmutableArray<DescribeRedFinding> ValidateLibrary(
        string repositoryRoot, IEnumerable<ScribeDocument> documents, LeanAxiomReport? leanReport,
        LibraryNoteCatalogInspection? libraryInspection = null,
        ProblemCandidateCatalogInspection? problemInspection = null, bool validateLocators = false)
    {
        var material = documents.ToImmutableArray();
        var generatedPaths = material.Select(document => document.Header.MirrorBlueprint.Path.Value)
            .ToHashSet(StringComparer.Ordinal);
        var inspected = libraryInspection ?? LibraryNoteCatalog.Inspect(repositoryRoot);
        var notes = inspected.Notes.GroupBy(note => note.BibKey.Value, StringComparer.Ordinal)
            .ToDictionary(group => group.Key, group => group.First(), StringComparer.Ordinal);
        var findings = ImmutableArray.CreateBuilder<DescribeRedFinding>();
        findings.AddRange(inspected.Findings.Select(finding => new DescribeRedFinding(finding.Code, finding.Path, finding.Message)));
        foreach (var document in material)
        {
            foreach (var anchor in document.Header.Anchors.OfType<LiteratureAnchor>())
                ValidateLiteratureAnchor(document.Header.Gid.Value, anchor, notes, findings);
            ValidateLibraryBlocks(document.Header.Gid.Value, document.Content, notes, findings);
        }
        foreach (var note in inspected.Notes)
        {
            foreach (var reference in note.StrataTouched)
                ValidateGid(repositoryRoot, note.RelativePath, reference, generatedPaths, leanReport, findings, "dangling-library-gid");
            if (note.Triage is LibraryTriage.Task task)
                ValidateGid(repositoryRoot, note.RelativePath, task.Reference, generatedPaths, leanReport, findings, "dangling-library-gid");
        }
        var problems = problemInspection ?? ProblemCandidateCatalog.Inspect(repositoryRoot);
        findings.AddRange(problems.Findings.Select(finding => new DescribeRedFinding(finding.Code, finding.Path, finding.Message)));
        foreach (var candidate in problems.Candidates) ValidateProblemSource(candidate, notes, findings);
        if (validateLocators && findings.Count == 0)
            findings.AddRange(DescribeContentGovernance.ValidateReferencedNoteLocators(repositoryRoot, material, inspected));
        return findings.OrderBy(finding => finding.Path, StringComparer.Ordinal)
            .ThenBy(finding => finding.Code, StringComparer.Ordinal).ThenBy(finding => finding.Message, StringComparer.Ordinal).ToImmutableArray();
    }

    private static void ValidateLibraryBlocks(string documentGid, BlockSequence blocks,
        IReadOnlyDictionary<string, LibraryNote> notes, ImmutableArray<DescribeRedFinding>.Builder findings)
    {
        foreach (var block in blocks.Items)
        {
            if (block is DocumentBlock.Section section)
                ValidateLibraryBlocks(documentGid, section.Content, notes, findings);
            if (block is not DocumentBlock.Describe describe) continue;
            if (describe.LiteratureReference is { } literature)
                ValidateLiterature(documentGid, literature, notes, findings);
            foreach (var acknowledgement in describe.AcknowledgementReferences)
                ValidateLiterature(documentGid, acknowledgement, notes, findings);
            ValidateLibraryBlocks(documentGid, describe.Content, notes, findings);
        }
    }
}
