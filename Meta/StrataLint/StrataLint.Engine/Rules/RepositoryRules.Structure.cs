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

    private static ImmutableArray<RuleFinding> Capacity(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var directories = new Dictionary<string, int>(StringComparer.Ordinal);
        foreach (var (path, file) in context.Current.Files)
        {
            if (path.Value.StartsWith("docs/develop/", StringComparison.Ordinal)
                || string.Equals(path.Value, "lake-manifest.json", StringComparison.Ordinal)
                || string.Equals(
                    path.Value,
                    BackfillInventoryLoader.RelativePath,
                    StringComparison.Ordinal))
            {
                continue;
            }

            var lineCount = file.Text.Split('\n').Length - (file.Text.EndsWith('\n') ? 1 : 0);
            if (lineCount > 800)
            {
                findings.Add(new RuleFinding(path.Value, "artifact exceeds 800 lines"));
            }
            else if (lineCount > 600)
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
            .Where(static item => item.Value > 12)
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

        return CanonicalStatementWriter.WriteModule(repoPath, baseline).AsSpan()
            .SequenceEqual(CanonicalStatementWriter.WriteModule(repoPath, current).AsSpan())
                ? ImmutableArray<RuleFinding>.Empty
                : ImmutableArray.Create(new RuleFinding(path, "semantic declaration identities and types are frozen"));
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
}
