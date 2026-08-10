using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    internal const string HeartsPath = "D5/X_Frontier/Hearts.lean";

    private static ImmutableArray<RuleFinding> Imports(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var (path, report) in context.Lean.Report.Files.OrderBy(item => item.Key.Value, StringComparer.Ordinal))
        {
            foreach (var module in report.Imports.Where(static item => item.StartsWith("D5.", StringComparison.Ordinal)))
            {
                var target = module.Replace('.', '/') + ".lean";
                if (!context.Current.TryGetFile(target, out _))
                {
                    findings.Add(new RuleFinding(path.Value, $"managed import {target} does not exist"));
                }
                else if (!ImportAllowed(path.Value, target))
                {
                    findings.Add(new RuleFinding(path.Value, $"stratum closure may not import {target}"));
                }
            }
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Sorry(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var (path, report) in context.Lean.Report.Files)
        {
            var declarations = report.Declarations
                .Where(static item => item.Axioms.Contains("sorryAx", StringComparer.Ordinal))
                .Select(static item => item.Name)
                .Order(StringComparer.Ordinal)
                .ToArray();
            if (declarations.Length > 0 && !path.Value.Contains("/X_Frontier/", StringComparison.Ordinal))
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    "sorryAx occurs in declaration closure: " + string.Join(", ", declarations)));
            }
        }

        return findings.ToImmutable();
    }

    // SL-003 capacity limits. These are the single enforcement source shared by
    // the admission rule (Capacity, below) and the ArchitectureTests CapacityPolicy
    // dotnet-test net, so both agree on the exact thresholds with no drift.
    internal const int ArtifactHardLineLimit = 800;

    internal const int ArtifactSoftLineLimit = 600;

    internal const int DirectoryFileLimit = 12;

    // The repository-wide capacity net tolerates a band above the admission limit.
    // Capacity is pressure, not correctness: an overfull bucket is a signal to split
    // (CLAUDE.md 8), and by the tiers of 20 a reversible content-level fact belongs in
    // detect-and-correct. Without the band, two PRs branched from the same base can each
    // add one file to a bucket holding eleven, each see twelve and admit, and their union
    // of thirteen turns the repository-wide scan red - blocking every unrelated PR until
    // someone splits. That is what made strict (now forbidden, 19) load-bearing. The
    // admission rule keeps the unbanded limit, so the next change touching that bucket is
    // still refused and the split pressure lands exactly where it belongs.
    internal const int DirectoryToleranceLimit = 24;

    // SL-003 capacity exclusions: theory inputs, the Lake manifest, the backfill
    // inventory, atomizer dialect registry, canonical CAS blobs, per-atom
    // formalization receipts, and emitted Blueprint projections are not artifacts
    // the capacity pressure rule bounds. Machine inventories grow one entry per
    // admitted unit and are never navigated as content buckets; the atomizer registry
    // is one canonical strict-loader input, not a content artifact to split. A
    // Blueprint document's structural slot is its .scribe.cs source (FILEMAP
    // kind=generated for the .md, produced by ScribeEmitter and verified by
    // its producer); its GID must name an existing Lean module and the definition path
    // is bijective with that GID, so bounding the projections would cap a lawful
    // twelve-module Lean bucket at six blueprinted modules. Single source shared with
    // the CapacityPolicy dotnet-test net.
    internal static bool IsCapacityExcluded(string path) =>
        path.StartsWith("docs/develop/", StringComparison.Ordinal)
        || string.Equals(path, "lake-manifest.json", StringComparison.Ordinal)
        || string.Equals(path, BackfillInventoryLoader.RelativePath, StringComparison.Ordinal)
        || path.StartsWith(BackfillInventoryLoader.RootPath, StringComparison.Ordinal)
        || string.Equals(path, TheoryAtomizerDataLoader.DataPath, StringComparison.Ordinal)
        || DigestionCasStore.IsCanonicalPath(path)
        || FrozenLedgerChangeClassifier.IsAcceptedEventPath(path)
        || path.StartsWith(DigestionFormalizationReceipt.RootPath, StringComparison.Ordinal)
        || (path.StartsWith("Blueprint/", StringComparison.Ordinal)
            && path.EndsWith(".md", StringComparison.Ordinal));

    // The canonical artifact line count: newline-delimited lines, not counting a
    // trailing terminator. Shared with CapacityPolicy so both nets agree exactly.
    internal static int CountArtifactLines(string text) =>
        text.Split('\n').Length - (text.EndsWith('\n') ? 1 : 0);

    private static ImmutableArray<RuleFinding> Capacity(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var directories = new Dictionary<string, int>(StringComparer.Ordinal);
        foreach (var (path, file) in context.Current.Files)
        {
            if (IsCapacityExcluded(path.Value))
            {
                continue;
            }

            var lineCount = CountArtifactLines(file.Text);
            if (lineCount > ArtifactHardLineLimit)
            {
                findings.Add(new RuleFinding(path.Value, "artifact exceeds 800 lines"));
            }
            else if (lineCount > ArtifactSoftLineLimit)
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    $"artifact spans {lineCount} lines (soft limit 600, hard limit 800)",
                    AdmissionEffect.Observe));
            }

            var slash = path.Value.LastIndexOf('/');
            var directory = slash < 0 ? "." : path.Value[..slash];
            directories[directory] = directories.GetValueOrDefault(directory) + 1;
        }

        findings.AddRange(directories
            .Where(static item => item.Value > DirectoryFileLimit)
            .Select(static item => new RuleFinding(
                item.Key,
                $"directory contains {item.Value} files (maximum 12)")));
        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Mirrors(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var (path, file) in FormalFiles(context.Current))
        {
            if (!TryHeader(file.Text, out var header))
            {
                continue;
            }

            ValidateMirror(path.Value, "mirror-B", header.MirrorB, "D5/B/", context.Current, findings);
            ValidateMirror(path.Value, "mirror-E", header.MirrorE, "D5/E/", context.Current, findings);
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Chronicle(RuleEvaluationContext context) =>
        context.Baseline.Files
            .Where(static item => item.Key.Value.StartsWith("Chronicle/", StringComparison.Ordinal))
            .Where(item => !context.Current.TryGetFile(item.Key.Value, out var current)
                || !current.RawBytes.AsSpan().SequenceEqual(item.Value.RawBytes.AsSpan()))
            .Select(static item => new RuleFinding(item.Key.Value, "tracked Chronicle entries are append-only"))
            .ToImmutableArray();

    private static ImmutableArray<RuleFinding> Badges(RuleEvaluationContext context) =>
        context.Current.Files
            .Where(static item => IsStatusScope(item.Key.Value) && BadgePattern.IsMatch(item.Value.Text))
            .Select(static item => new RuleFinding(item.Key.Value, "hand-written status badge is forbidden"))
            .ToImmutableArray();

    private static ImmutableArray<RuleFinding> Hearts(RuleEvaluationContext context)
    {
        const string path = HeartsPath;
        ImmutableArray<HeartsAuthorizationEntry> authorizations;
        try
        {
            authorizations = HeartsAuthorizationLedger.ReadAppendOnly(
                context.Current,
                context.Baseline);
        }
        catch (FormatException exception)
        {
            return ImmutableArray.Create(
                new RuleFinding(HeartsAuthorizationLedger.Path, exception.Message));
        }

        var hadBaseline = context.Baseline.TryGetFile(path, out _);
        var hasCurrent = context.Current.TryGetFile(path, out _);
        if (hadBaseline && !hasCurrent)
        {
            return ImmutableArray.Create(new RuleFinding(path, "frozen Hearts.lean was deleted"));
        }

        if (!hadBaseline && hasCurrent)
        {
            return ImmutableArray.Create(new RuleFinding(path, "new Hearts.lean requires a human-gated baseline"));
        }

        if (!hadBaseline)
        {
            return ImmutableArray<RuleFinding>.Empty;
        }

        if (!RepoPath.TryCreate(path, out var repoPath)
            || !context.BaselineLean.Report.Files.TryGetValue(repoPath, out var baseline)
            || !context.Lean.Report.Files.TryGetValue(repoPath, out var current))
        {
            return ImmutableArray.Create(new RuleFinding(path, "protected Hearts baseline has no semantic report"));
        }

        if (!string.IsNullOrEmpty(baseline.Error))
        {
            return ImmutableArray.Create(new RuleFinding(path, "protected Hearts baseline has no semantic report"));
        }

        if (!string.IsNullOrEmpty(current.Error))
        {
            return ImmutableArray.Create(new RuleFinding(path, $"Hearts semantic report failed: {current.Error}"));
        }

        if (CanonicalStatementWriter.WriteModule(repoPath, baseline).AsSpan()
            .SequenceEqual(CanonicalStatementWriter.WriteModule(repoPath, current).AsSpan()))
        {
            return ImmutableArray<RuleFinding>.Empty;
        }

        var baselineStatements = CanonicalStatementWriter.DeclarationStatementIds(repoPath, baseline);
        var currentStatements = CanonicalStatementWriter.DeclarationStatementIds(repoPath, current);
        var addedStatements = currentStatements.Except(baselineStatements).ToImmutableArray();
        var isExactSingleAppend = currentStatements.Length == baselineStatements.Length + 1
            && addedStatements.Length == 1
            && baselineStatements.All(currentStatements.Contains);
        if (isExactSingleAppend)
        {
            var addedStatement = addedStatements[0];
            var declarations = current.Declarations
                .Where(declaration => declaration.IncludeInStatement
                    && declaration.NameKey == addedStatement.DeclarationNameKey
                    && declaration.Kind == addedStatement.Kind)
                .ToImmutableArray();
            if (declarations.Length == 1)
            {
                if (authorizations.Any(entry =>
                    entry.StatementName == declarations[0].Name
                    && entry.StatementSha256
                        == addedStatement.StatementId.Value["sha256:".Length..]))
                {
                    return ImmutableArray<RuleFinding>.Empty;
                }
            }
        }

        return ImmutableArray.Create(
            new RuleFinding(path, "semantic declaration identities and types are frozen"));
    }

    private static ImmutableArray<RuleFinding> Generality(RuleEvaluationContext context)
    {
        var headers = FormalFiles(context.Current)
            .Select(item => (item.Path, Header: TryHeader(item.File.Text, out var header) ? header : null))
            .Where(static item => item.Header is not null)
            .ToDictionary(static item => item.Path.Value, static item => item.Header, StringComparer.Ordinal);
        var imports = context.Lean.Report.Files.ToDictionary(
            static item => item.Key.Value,
            static item => item.Value.Imports
                .Where(static module => module.StartsWith("D5.", StringComparison.Ordinal))
                .Select(static module => module.Replace('.', '/') + ".lean")
                .ToImmutableArray(),
            StringComparer.Ordinal);
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var (source, header) in headers)
        {
            if (header?.Generality != "G")
            {
                continue;
            }

            foreach (var target in ImportClosure(source, imports))
            {
                if (headers.TryGetValue(target, out var imported)
                    && imported?.Generality is "I" or "E")
                {
                    findings.Add(new RuleFinding(
                        source,
                        $"G artifact imports {imported.Generality} fact {target}"));
                }
            }
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Domains(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var path in context.Current.Files.Keys)
        {
            var parts = path.Value.Split('/');
            int stratumIndex;
            string label;
            if (parts.Length >= 4 && parts[0] == "D5")
            {
                stratumIndex = 1;
                label = "domain";
            }
            else if (parts.Length >= 5
                && (parts[0] is "Blueprint" or "Evidence")
                && parts[1] == "D5")
            {
                stratumIndex = 2;
                label = parts[0] == "Blueprint" ? "mirror domain" : "domain";
            }
            else
            {
                continue;
            }

            if (!IsStratum(parts[stratumIndex]))
            {
                continue;
            }

            var stratum = parts[stratumIndex];
            var domain = parts[stratumIndex + 1];
            var policyDomain = context.Policy.Domains.FirstOrDefault(
                item => string.Equals(item.Key.Value, domain, StringComparison.Ordinal));
            if (policyDomain.Key is null)
            {
                findings.Add(new RuleFinding(path.Value, $"{label} '{domain}' is not controlled"));
            }
            else if (!string.Equals(policyDomain.Value.ToString(), stratum, StringComparison.Ordinal))
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    $"domain {domain} belongs to {policyDomain.Value}, not {stratum}"));
            }
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Headers(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var headers = new List<(RepoPath Path, HeaderData Header)>();
        var counts = new Dictionary<string, int>(StringComparer.Ordinal);
        foreach (var (path, file) in FormalFiles(context.Current))
        {
            if (!TryHeader(file.Text, out var header))
            {
                findings.Add(new RuleFinding(path.Value, "expected the exact six-line header at byte zero"));
                continue;
            }

            headers.Add((path, header));
            counts[header.Gid] = counts.GetValueOrDefault(header.Gid) + 1;
        }

        foreach (var (path, header) in headers)
        {
            var expected = path.Value[..^5];
            if (counts[header.Gid] == 1
                && Gid.TryParse(header.Gid, out _)
                && !string.Equals(header.Gid, expected, StringComparison.Ordinal))
            {
                findings.Add(new RuleFinding(path.Value, $"GID '{header.Gid}' does not match '{expected}'"));
            }
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Tasks(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var current = CollectTasks(context.Current, findings);
        var baseline = CollectTasks(context.Baseline, null);
        foreach (var duplicate in current.Where(static item => item.Value.Count > 1))
        {
            findings.Add(new RuleFinding(duplicate.Value[0].Path, $"task code {duplicate.Key} is duplicated"));
        }

        foreach (var (code, entries) in current)
        {
            foreach (var entry in entries.Where(static entry =>
                entry.Autopsy.Contains("[codex-failed]", StringComparison.Ordinal)
                && !HasValidCodexLogReference(entry.Autopsy)))
            {
                findings.Add(new RuleFinding(
                    entry.Path,
                    $"codex-failed autopsy for {code} requires a valid [codex-log:<rooted-path>] reference"));
            }
        }

        foreach (var (code, entries) in baseline)
        {
            if (!current.TryGetValue(code, out var currentEntries))
            {
                findings.Add(new RuleFinding(entries[0].Path, $"permanent task code {code} was removed"));
            }
            else if (entries[0].Autopsy != "none"
                && !currentEntries[0].Autopsy.Contains(entries[0].Autopsy, StringComparison.Ordinal))
            {
                findings.Add(new RuleFinding(currentEntries[0].Path, $"autopsy for {code} was shortened"));
            }
        }

        return findings.ToImmutable();
    }

    private static bool HasValidCodexLogReference(string autopsy) =>
        CodexLogReferencePattern.Matches(autopsy)
            .Select(static match => match.Groups["path"].Value)
            .Any(IsValidCodexLogPath);

    private static bool IsValidCodexLogPath(string path)
    {
        string relative;
        if (path.StartsWith("<RT>/", StringComparison.Ordinal))
        {
            relative = path[5..];
        }
        else if (path.StartsWith("~/", StringComparison.Ordinal))
        {
            relative = path[2..];
        }
        else if (path.StartsWith("/", StringComparison.Ordinal))
        {
            relative = path[1..];
        }
        else
        {
            return false;
        }

        // This walking skeleton validates portable citation syntax only. Codex logs and
        // receipts are host/runtime-local, so checking path existence would reject valid
        // citations on CI runners that cannot share the originating filesystem (#707).
        var segments = relative.Split('/');
        return segments.Length > 0 && segments.All(static segment =>
            segment.Length > 0
            && segment is not "." and not ".."
            && segment.All(static character =>
                char.IsAsciiLetterOrDigit(character) || character is '.' or '_' or '-'));
    }
}
