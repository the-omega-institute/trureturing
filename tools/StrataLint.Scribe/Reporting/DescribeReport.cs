using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Scribe;

internal sealed record DescribeNodeRecord(
    string NodeId,
    string DocumentGid,
    string Kind,
    string Title,
    string StatementKind,
    string FormulaProvenance,
    string? ProjectionFailureReason,
    string Provenance,
    string? LiteratureGid,
    ImmutableArray<string> AcknowledgementGids);

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
        ImmutableArray<DescribeNodeRecord> unprojectable,
        ImmutableArray<DescribeRedFinding> redFindings,
        ImmutableArray<DescribeObservation> observations)
    {
        NodeStats = nodeStats;
        Nodes = nodes;
        SuspectedNovel = suspectedNovel;
        Unprojectable = unprojectable;
        RedFindings = redFindings;
        Observations = observations;
    }

    internal const string CaseId = "DESCRIBE-NODES";

    internal DescribeNodeStats NodeStats { get; }

    internal ImmutableArray<DescribeNodeRecord> Nodes { get; }

    internal ImmutableArray<DescribeNodeRecord> SuspectedNovel { get; }

    internal ImmutableArray<DescribeNodeRecord> Unprojectable { get; }

    internal ImmutableArray<DescribeRedFinding> RedFindings { get; }

    internal ImmutableArray<DescribeObservation> Observations { get; }

    internal int ProjectionOpenCount => Unprojectable.Length;

    // Two states, not three. "needs-classification" counted nodes whose provenance was unassessed,
    // and no node can carry that any more: the interface only accepts an assessed provenance, so the
    // branch was unreachable and the count it read was structurally zero.
    internal string Status => RedFindings.IsEmpty ? "classified" : "invalid";

    internal static DescribeReport Build(
        string repositoryRoot,
        IEnumerable<ScribeDocument> documents,
        StrataLint.Engine.LeanAxiomReport? leanReport = null,
        bool validateContentGovernance = false)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(documents);
        var material = documents
            .OrderBy(static document => document.Header.Gid.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        return BuildCore(
            repositoryRoot,
            material,
            leanReport,
            validateContentGovernance,
            leanSourcePaths: null,
            libraryInspection: null);
    }

    internal static DescribeReport BuildIncremental(
        string repositoryRoot,
        IEnumerable<ScribeDocument> documents,
        IEnumerable<string> changedPaths,
        LeanAxiomReport? leanReport = null,
        bool validateContentGovernance = false)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(documents);
        ArgumentNullException.ThrowIfNull(changedPaths);
        var universe = documents
            .OrderBy(static document => document.Header.Gid.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        // 只有 Lean docstring 观察是可分区的:每条只由单个 Lean 文件的行导出,且从不进
        // RedFindings。文档集与全部红判词一律走全量 —— Blueprint 定义之间存在普通 C#
        // 编译期依赖(Documents.csproj 把全部 *.scribe.cs 编入同一程序集,
        // DocumentDefinitions 标注 CompileTimeInputUniverse),按 changed paths 收窄
        // 会让受影响但未改动的文档静默通过,与 #4439 同一机制。见 #5634。
        return BuildCore(
            repositoryRoot,
            universe,
            leanReport,
            validateContentGovernance,
            changedPaths.ToImmutableArray(),
            libraryInspection: null);
    }

    private static DescribeReport BuildCore(
        string repositoryRoot,
        ImmutableArray<ScribeDocument> material,
        LeanAxiomReport? leanReport,
        bool validateContentGovernance,
        IEnumerable<string>? leanSourcePaths,
        LibraryNoteCatalogInspection? libraryInspection)
    {
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

        observations.AddRange(ObserveLeanDocstrings(repositoryRoot, leanSourcePaths));
        libraryInspection ??= LibraryNoteCatalog.Inspect(repositoryRoot);
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
        var redFindings = DescribeRepositoryValidator.Validate(
            repositoryRoot,
            material,
            leanReport,
            libraryInspection).ToBuilder();
        if (validateContentGovernance)
        {
            redFindings.AddRange(DescribeContentGovernance.Validate(
                repositoryRoot,
                material,
                stats,
                libraryInspection));
        }

        return new DescribeReport(
            stats,
            orderedNodes,
            orderedNodes.Where(static node => node.Provenance == "suspected-novel").ToImmutableArray(),
            orderedNodes.Where(static node => node.ProjectionFailureReason is not null).ToImmutableArray(),
            redFindings
                .OrderBy(static finding => finding.Path, StringComparer.Ordinal)
                .ThenBy(static finding => finding.Code, StringComparer.Ordinal)
                .ThenBy(static finding => finding.Message, StringComparer.Ordinal)
                .ToImmutableArray(),
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
                    var nodeId = $"{documentGid}#describe/{describe.Id.Value}";
                    nodes.Add(new DescribeNodeRecord(
                        nodeId,
                        documentGid,
                        DescribeVocabulary.CanonicalName(describe.Kind),
                        describe.Title.Value,
                        describe.Statement is DescribeStatement.FormulaAst
                            ? "formula"
                            : "lean-declaration",
                        describe.FormulaProvenance == StatementFormulaProvenance.LeanDerived ? "lean-derived" : "hand-authored",
                        ProjectionFailure(describe),
                        DescribeVocabulary.CanonicalName(describe.ProvenanceKind),
                        describe.LiteratureReference?.Value,
                        describe.AcknowledgementReferences
                            .Select(static reference => reference.Value)
                            .ToImmutableArray()));
                    if (string.Equals(describe.Id.Value, PlainSlug(describe.Title.Value), StringComparison.Ordinal))
                    {
                        observations.Add(new DescribeObservation(
                            "title-derived-id",
                            nodeId,
                            $"Describe ID equals the plain title slug: {describe.Id.Value}"));
                    }
                    if (describe.Statement is DescribeStatement.LeanDeclaration lean
                        && !string.Equals(documentGid, DeclarationModule(lean.Value.Value), StringComparison.Ordinal))
                    {
                        observations.Add(new DescribeObservation(
                            "cross-module-lean-declaration",
                            nodeId,
                            $"Lean declaration {lean.Value.Value} is outside document module {documentGid}"));
                    }
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

    private static string? ProjectionFailure(DocumentBlock.Describe describe)
    {
        if (describe.Statement is not DescribeStatement.LeanDeclaration lean
            || !ScribeDescribeContract.RequiresLatex(DescribeVocabulary.CanonicalName(describe.Kind))) return null;
        return StatementProjectionFixtureLoader.Project(lean.Value) is ProjectionOutcome.Unprojectable failed
            ? failed.Reason : null;
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

    private static ImmutableArray<DescribeObservation> ObserveLeanDocstrings(
        string repositoryRoot,
        IEnumerable<string>? sourcePaths)
    {
        var root = Path.Combine(repositoryRoot, "D5");
        if (!Directory.Exists(root))
        {
            return [];
        }

        var observations = ImmutableArray.CreateBuilder<DescribeObservation>();
        var paths = sourcePaths is null
            ? Directory.EnumerateFiles(root, "*.lean", SearchOption.AllDirectories)
            : sourcePaths
                .Where(static path => path.StartsWith("D5/", StringComparison.Ordinal)
                    && path.EndsWith(".lean", StringComparison.Ordinal))
                .Select(path => Path.Combine(repositoryRoot, path))
                .Where(File.Exists);
        foreach (var path in paths.Order(StringComparer.Ordinal))
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

    private static string PlainSlug(string value) =>
        string.Join(
            '-',
            value.ToLowerInvariant()
                .Split([' ', '\t', '\r', '\n'], StringSplitOptions.RemoveEmptyEntries)
                .Select(static word => new string(word.Where(char.IsLetterOrDigit).ToArray()))
                .Where(static word => word.Length > 0));

    private static string DeclarationModule(string value)
    {
        var separator = value.LastIndexOf('.');
        return separator < 0 ? string.Empty : value[..separator];
    }

    private static bool IsUnicodeFormulaCharacter(char value) => value is
        'φ' or 'ψ' or '∈' or '∉' or '≤' or '≥' or '→' or '↔' or '∑' or '∏'
        or '₀' or '₁' or '₂' or '₃' or '₄' or '₅' or '₆' or '₇' or '₈' or '₉';

}
