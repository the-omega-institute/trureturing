using System.Collections.Immutable;
using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.Scribe;

internal static class DescribeContentGovernance
{
    private static readonly string[] ForbiddenSourceTerms =
    [
        "FormulaTokens",
        "Formula.TokenTree",
        "FormulaToken",
        "FormulaMark",
        "FormulaSpace",
    ];

    internal static ImmutableArray<DescribeRedFinding> ValidateSources(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var blueprintRoot = Path.Combine(repositoryRoot, "Blueprint");
        if (!Directory.Exists(blueprintRoot)) return [];

        var findings = ImmutableArray.CreateBuilder<DescribeRedFinding>();
        foreach (var path in Directory.EnumerateFiles(
                     blueprintRoot,
                     "*.scribe.cs",
                     SearchOption.AllDirectories).Order(StringComparer.Ordinal))
        {
            var relativePath = Path.GetRelativePath(repositoryRoot, path)
                .Replace(Path.DirectorySeparatorChar, '/');
            var source = File.ReadAllText(path);
            foreach (var term in ForbiddenSourceTerms.Where(term =>
                         source.Contains(term, StringComparison.Ordinal)))
            {
                findings.Add(new DescribeRedFinding(
                    "linear-formula-token",
                    relativePath,
                    $"Blueprint author source contains forbidden linear formula token API '{term}'"));
            }

            var relativeDirectory = Path.GetDirectoryName(
                Path.GetRelativePath(blueprintRoot, path));
            var expectedNamespace = "StrataLint.Scribe.Blueprint"
                + (string.IsNullOrEmpty(relativeDirectory)
                    ? string.Empty
                    : "." + relativeDirectory.Replace(Path.DirectorySeparatorChar, '.'));
            var namespaces = Regex.Matches(
                    source,
                    @"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_.]*)\s*(?:;|\{)",
                    RegexOptions.Multiline | RegexOptions.CultureInvariant)
                .Select(static match => match.Groups[1].Value)
                .ToArray();
            if (namespaces.Length != 1
                || !string.Equals(namespaces[0], expectedNamespace, StringComparison.Ordinal))
            {
                findings.Add(new DescribeRedFinding(
                    "blueprint-namespace",
                    relativePath,
                    $"source must declare exactly namespace {expectedNamespace}"));
            }
        }

        return Order(findings);
    }

    internal static ImmutableArray<DescribeRedFinding> Validate(
        string repositoryRoot,
        ImmutableArray<ScribeDocument> documents,
        DescribeNodeStats reportStats,
        LibraryNoteCatalogInspection libraryInspection)
    {
        var findings = ValidateSources(repositoryRoot).ToBuilder();
        ValidateCensus(repositoryRoot, documents, findings);
        ValidateIndependentInventory(documents, reportStats, findings);
        ValidateReferencedNoteLocators(repositoryRoot, documents, libraryInspection, findings);
        return Order(findings);
    }

    private static void ValidateCensus(
        string repositoryRoot,
        ImmutableArray<ScribeDocument> documents,
        ImmutableArray<DescribeRedFinding>.Builder findings)
    {
        var documentGids = documents
            .Select(static document => document.Header.Gid.Value)
            .ToImmutableHashSet(StringComparer.Ordinal);
        var census = ReceiptFreeDocumentCatalog.Load(repositoryRoot, documents);
        var receiptBound = BackfillInventoryLoader.LoadTrustedRoot(repositoryRoot)
            .RequireDigestionEntries()
            .SelectMany(static entry => entry.Receipts.Scribe)
            .Select(static receipt => ScribeEmissionAttestation.DocumentGid(receipt.Gid))
            .ToImmutableHashSet(StringComparer.Ordinal);
        var expectedBound = receiptBound.Intersect(documentGids, StringComparer.Ordinal)
            .ToImmutableHashSet(StringComparer.Ordinal);
        var expectedFree = documentGids.Except(receiptBound, StringComparer.Ordinal)
            .ToImmutableHashSet(StringComparer.Ordinal);
        var overlap = census.ReceiptFreeDocumentGids
            .Intersect(census.ReceiptBoundDocumentGids, StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        var classified = census.ReceiptFreeDocumentGids
            .Union(census.ReceiptBoundDocumentGids, StringComparer.Ordinal)
            .ToImmutableHashSet(StringComparer.Ordinal);
        if (overlap.Length != 0
            || !classified.SetEquals(documentGids)
            || !census.ReceiptBoundDocumentGids.SetEquals(expectedBound)
            || !census.ReceiptFreeDocumentGids.SetEquals(expectedFree)
            || expectedBound.IsEmpty
            || expectedFree.IsEmpty
            || census.ReceiptFreeDocumentGids.Count + census.ReceiptBoundDocumentGids.Count
                != documents.Length)
        {
            findings.Add(new DescribeRedFinding(
                "receipt-census",
                "Meta/Digestion/backfill",
                "receipt-free and receipt-bound document sets must be disjoint and complete"));
        }
    }

    internal static ImmutableArray<DescribeRedFinding> ValidateIndependentInventory(
        ImmutableArray<ScribeDocument> documents,
        DescribeNodeStats reportStats)
    {
        var findings = ImmutableArray.CreateBuilder<DescribeRedFinding>();
        ValidateIndependentInventory(documents, reportStats, findings);
        return Order(findings);
    }

    private static void ValidateIndependentInventory(
        ImmutableArray<ScribeDocument> documents,
        DescribeNodeStats reportStats,
        ImmutableArray<DescribeRedFinding>.Builder findings)
    {
        var blocks = documents.SelectMany(static document => EnumerateBlocks(document.Content)).ToArray();
        var nodes = blocks.OfType<DocumentBlock.Describe>().ToArray();
        var byKind = nodes
            .GroupBy(static node => DescribeVocabulary.CanonicalName(node.Kind), StringComparer.Ordinal)
            .ToImmutableSortedDictionary(
                static group => group.Key,
                static group => group.Count(),
                StringComparer.Ordinal);
        var byProvenance = nodes
            .GroupBy(
                static node => DescribeVocabulary.CanonicalName(node.ProvenanceKind),
                StringComparer.Ordinal)
            .ToImmutableSortedDictionary(
                static group => group.Key,
                static group => group.Count(),
                StringComparer.Ordinal);
        var formulaContentSlots = blocks.OfType<DocumentBlock.DisplayFormula>().Count()
            + blocks.OfType<DocumentBlock.Paragraph>().Sum(static paragraph =>
                paragraph.Content.Items.Count(static inline => inline is Inline.InlineFormula));
        if (nodes.Length != reportStats.Total
            || formulaContentSlots != reportStats.FormulaContentSlots
            || nodes.Count(static node => node.Statement is DescribeStatement.FormulaAst)
                != reportStats.FormulaStatements
            || nodes.Count(static node => node.Statement is DescribeStatement.LeanDeclaration)
                != reportStats.LeanStatements
            || !byKind.SequenceEqual(reportStats.ByKind)
            || !byProvenance.SequenceEqual(reportStats.ByProvenance))
        {
            findings.Add(new DescribeRedFinding(
                "describe-ast-inventory",
                "Blueprint",
                "describe report statistics disagree with an independent AST inventory"));
        }

        if (nodes.Any(static node =>
                node.ProvenanceKind == DescribeProvenanceKind.SuspectedNovel))
        {
            findings.Add(new DescribeRedFinding(
                "suspected-novel",
                "Blueprint",
                "production Describe corpus must not contain suspected-novel nodes"));
        }
    }

    internal static ImmutableArray<DescribeRedFinding> ValidateReferencedNoteLocators(
        string repositoryRoot,
        ImmutableArray<ScribeDocument> documents,
        LibraryNoteCatalogInspection libraryInspection)
    {
        var findings = ImmutableArray.CreateBuilder<DescribeRedFinding>();
        ValidateReferencedNoteLocators(repositoryRoot, documents, libraryInspection, findings);
        return Order(findings);
    }

    private static void ValidateReferencedNoteLocators(
        string repositoryRoot,
        ImmutableArray<ScribeDocument> documents,
        LibraryNoteCatalogInspection libraryInspection,
        ImmutableArray<DescribeRedFinding>.Builder findings)
    {
        var notes = libraryInspection.Notes.ToDictionary(
            static note => note.BibKey.Value,
            StringComparer.Ordinal);
        var references = documents
            .SelectMany(static document => document.Header.Anchors
                .OfType<LiteratureAnchor>()
                .Select(static anchor => anchor.BibKey.Value)
                .Concat(EnumerateBlocks(document.Content)
                    .OfType<DocumentBlock.Describe>()
                    .SelectMany(ReferencedNotes)
                    .Select(static reference => reference.BibKey.Value)))
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal);
        foreach (var bibkey in references)
        {
            if (!notes.TryGetValue(bibkey, out var note)) continue;
            var text = File.ReadAllText(Path.Combine(repositoryRoot, note.RelativePath));
            const string verifiedHeading = "\n## Verified locator\n";
            const string locatorHeading = "\n## Locator\n";
            var locator = text.IndexOf(verifiedHeading, StringComparison.Ordinal);
            var headingLength = verifiedHeading.Length;
            if (locator < 0)
            {
                locator = text.IndexOf(locatorHeading, StringComparison.Ordinal);
                headingLength = locatorHeading.Length;
            }
            var body = locator < 0
                ? string.Empty
                : text[(locator + headingLength)..].Split("\n## ", 2)[0];
            var bindsDoi = note.Doi is null
                || body.Contains(note.Doi.Value, StringComparison.OrdinalIgnoreCase);
            var canonicalAnchorComplete = bibkey != "watrous2018theory"
                || body.Contains("Section 4.4", StringComparison.Ordinal)
                    && text.Contains(
                        "No specific theorem number is attributed",
                        StringComparison.Ordinal);
            if (string.IsNullOrWhiteSpace(body) || !bindsDoi || !canonicalAnchorComplete)
            {
                findings.Add(new DescribeRedFinding(
                    "incomplete-library-locator",
                    note.RelativePath,
                    $"referenced Library note {bibkey} must bind its DOI and retain its "
                        + "canonical verified locator scope"));
            }
        }
    }

    private static IEnumerable<LibraryNoteRef> ReferencedNotes(DocumentBlock.Describe describe)
    {
        if (describe.LiteratureReference is { } literature) yield return literature;
        foreach (var acknowledgement in describe.AcknowledgementReferences)
        {
            yield return acknowledgement;
        }
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

    private static ImmutableArray<DescribeRedFinding> Order(
        IEnumerable<DescribeRedFinding> findings) => findings
        .OrderBy(static finding => finding.Path, StringComparer.Ordinal)
        .ThenBy(static finding => finding.Code, StringComparer.Ordinal)
        .ThenBy(static finding => finding.Message, StringComparer.Ordinal)
        .ToImmutableArray();
}
