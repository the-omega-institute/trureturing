using System.Collections.Immutable;

namespace StrataLint.Scribe;

internal sealed record DescribeNodeRecord(
    string NodeId,
    string DocumentGid,
    string Kind,
    string Title,
    string StatementKind,
    string Provenance,
    string? LiteratureGid);

internal sealed record DescribeObservation(string Code, string Path, string Detail);

internal sealed record DescribeNodeStats(
    int Total,
    int FormulaContentSlots,
    int FormulaStatements,
    int LeanStatements,
    ImmutableSortedDictionary<string, int> ByKind,
    ImmutableSortedDictionary<string, int> ByProvenance);

internal sealed class DescribeReport
{
    private DescribeReport(
        DescribeNodeStats nodeStats,
        ImmutableArray<DescribeNodeRecord> nodes,
        ImmutableArray<DescribeNodeRecord> suspectedNovel,
        ImmutableArray<DescribeNodeRecord> unassessed,
        ImmutableArray<DescribeRedFinding> redFindings,
        ImmutableArray<DescribeObservation> observations)
    {
        NodeStats = nodeStats;
        Nodes = nodes;
        SuspectedNovel = suspectedNovel;
        Unassessed = unassessed;
        RedFindings = redFindings;
        Observations = observations;
    }

    internal const string CaseId = "DESCRIBE-NODES";

    internal DescribeNodeStats NodeStats { get; }

    internal ImmutableArray<DescribeNodeRecord> Nodes { get; }

    internal ImmutableArray<DescribeNodeRecord> SuspectedNovel { get; }

    internal ImmutableArray<DescribeNodeRecord> Unassessed { get; }

    internal ImmutableArray<DescribeRedFinding> RedFindings { get; }

    internal ImmutableArray<DescribeObservation> Observations { get; }

    internal int OpenCount => Unassessed.Length;

    internal string Status => !RedFindings.IsEmpty
        ? "invalid"
        : OpenCount > 0
            ? "needs-classification"
            : "classified";

    internal static DescribeReport Build(
        string repositoryRoot,
        IEnumerable<ScribeDocument> documents,
        StrataLint.Engine.LeanAxiomReport? leanReport = null)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(documents);
        var material = documents
            .OrderBy(static document => document.Header.Gid.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        var nodes = ImmutableArray.CreateBuilder<DescribeNodeRecord>();
        var observations = ImmutableArray.CreateBuilder<DescribeObservation>();
        var formulaContentSlots = 0;
        foreach (var document in material)
        {
            var textOrdinal = 0;
            VisitBlocks(
                document.Header.Gid.Value,
                document.Content,
                nodes,
                observations,
                ref textOrdinal,
                ref formulaContentSlots);
        }

        observations.AddRange(ObserveLeanDocstrings(repositoryRoot));
        var libraryInspection = LibraryNoteCatalog.Inspect(repositoryRoot);
        var notes = libraryInspection.Notes;
        observations.AddRange(notes
            .Where(static note => note.Doi is not null)
            .Select(static note => new DescribeObservation(
                "online-doi-title-check",
                note.RelativePath,
                $"offline hard gate did not resolve {note.Doi!.Value} or compare title {note.Title}")));

        var orderedNodes = nodes
            .OrderBy(static node => node.NodeId, StringComparer.Ordinal)
            .ToImmutableArray();
        var byKind = orderedNodes
            .GroupBy(static node => node.Kind, StringComparer.Ordinal)
            .ToImmutableSortedDictionary(
                static group => group.Key,
                static group => group.Count(),
                StringComparer.Ordinal);
        var byProvenance = orderedNodes
            .GroupBy(static node => node.Provenance, StringComparer.Ordinal)
            .ToImmutableSortedDictionary(
                static group => group.Key,
                static group => group.Count(),
                StringComparer.Ordinal);
        var stats = new DescribeNodeStats(
            orderedNodes.Length,
            formulaContentSlots,
            orderedNodes.Count(static node => node.StatementKind == "formula"),
            orderedNodes.Count(static node => node.StatementKind == "lean-declaration"),
            byKind,
            byProvenance);
        return new DescribeReport(
            stats,
            orderedNodes,
            orderedNodes.Where(static node => node.Provenance == "suspected-novel").ToImmutableArray(),
            orderedNodes.Where(static node => node.Provenance == "unassessed").ToImmutableArray(),
            DescribeRepositoryValidator.Validate(
                repositoryRoot,
                material,
                leanReport,
                libraryInspection),
            observations
                .OrderBy(static item => item.Path, StringComparer.Ordinal)
                .ThenBy(static item => item.Code, StringComparer.Ordinal)
                .ThenBy(static item => item.Detail, StringComparer.Ordinal)
                .ToImmutableArray());
    }

    private static void VisitBlocks(
        string documentGid,
        BlockSequence blocks,
        ImmutableArray<DescribeNodeRecord>.Builder nodes,
        ImmutableArray<DescribeObservation>.Builder observations,
        ref int textOrdinal,
        ref int formulaContentSlots)
    {
        foreach (var block in blocks.Items)
        {
            switch (block)
            {
                case DocumentBlock.Paragraph paragraph:
                    foreach (var inline in paragraph.Content.Items)
                    {
                        if (inline is Inline.InlineFormula)
                        {
                            formulaContentSlots++;
                        }
                        else if (inline is Inline.Text text)
                        {
                            textOrdinal++;
                            ObserveText(
                                text.Run.Value,
                                $"{documentGid}#text-{textOrdinal:D3}",
                                observations);
                        }
                    }
                    break;
                case DocumentBlock.DisplayFormula:
                    formulaContentSlots++;
                    break;
                case DocumentBlock.Section section:
                    VisitBlocks(
                        documentGid,
                        section.Content,
                        nodes,
                        observations,
                        ref textOrdinal,
                        ref formulaContentSlots);
                    break;
                case DocumentBlock.Describe describe:
                    nodes.Add(new DescribeNodeRecord(
                        $"{documentGid}#describe/{describe.Id.Value}",
                        documentGid,
                        DescribeVocabulary.CanonicalName(describe.Kind),
                        describe.Title.Value,
                        describe.Statement is DescribeStatement.FormulaAst
                            ? "formula"
                            : "lean-declaration",
                        DescribeVocabulary.CanonicalName(describe.Provenance.Kind),
                        describe.Provenance.LiteratureReference?.Value));
                    VisitBlocks(
                        documentGid,
                        describe.Content,
                        nodes,
                        observations,
                        ref textOrdinal,
                        ref formulaContentSlots);
                    break;
            }
        }
    }

    private static void ObserveText(
        string value,
        string path,
        ImmutableArray<DescribeObservation>.Builder observations)
    {
        if (value.Contains('`'))
        {
            observations.Add(new DescribeObservation(
                "code-span",
                path,
                "TextRun contains a code span that may encode a formula"));
        }

        if (value.Any(IsUnicodeFormulaCharacter))
        {
            observations.Add(new DescribeObservation(
                "unicode-suspected-formula",
                path,
                "TextRun contains a Unicode mathematical character"));
        }

        var outsideCode = string.Concat(value.Split('`').Where(static (_, index) => index % 2 == 0));
        if (outsideCode.Contains(" = ", StringComparison.Ordinal)
            || outsideCode.Contains("<->", StringComparison.Ordinal)
            || outsideCode.Contains("^", StringComparison.Ordinal))
        {
            observations.Add(new DescribeObservation(
                "plain-text-suspected-formula",
                path,
                "TextRun contains formula-like plain text"));
        }
    }

    private static ImmutableArray<DescribeObservation> ObserveLeanDocstrings(string repositoryRoot)
    {
        var root = Path.Combine(repositoryRoot, "D5");
        if (!Directory.Exists(root))
        {
            return [];
        }

        var observations = ImmutableArray.CreateBuilder<DescribeObservation>();
        foreach (var path in Directory.EnumerateFiles(root, "*.lean", SearchOption.AllDirectories)
                     .Order(StringComparer.Ordinal))
        {
            var inDocstring = false;
            var lines = File.ReadAllLines(path);
            for (var index = 0; index < lines.Length; index++)
            {
                var line = lines[index];
                if (line.Contains("/--", StringComparison.Ordinal))
                {
                    inDocstring = true;
                }

                if (inDocstring && LooksLikeFormula(line))
                {
                    observations.Add(new DescribeObservation(
                        "lean-docstring-formula",
                        Path.GetRelativePath(repositoryRoot, path).Replace('\\', '/') + $":{index + 1}",
                        "Lean docstring contains formula-like text outside Scribe Formula AST"));
                }

                if (inDocstring && line.Contains("-/", StringComparison.Ordinal))
                {
                    inDocstring = false;
                }
            }
        }

        return observations.ToImmutable();
    }

    private static bool LooksLikeFormula(string value) =>
        value.Contains('=')
        || value.Contains("<->", StringComparison.Ordinal)
        || value.Contains('^')
        || value.Any(IsUnicodeFormulaCharacter);

    private static bool IsUnicodeFormulaCharacter(char value) => value is
        'φ' or 'ψ' or '∈' or '∉' or '≤' or '≥' or '→' or '↔' or '∑' or '∏'
        or '₀' or '₁' or '₂' or '₃' or '₄' or '₅' or '₆' or '₇' or '₈' or '₉';

}
