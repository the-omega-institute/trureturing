using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    /// <summary>The theory tree the digestion machine reads; its volumes are the append-only ones.</summary>
    private static bool IsTheoryVolumePath(string path) =>
        path.StartsWith("docs/develop/theory/", StringComparison.Ordinal);

    private static bool ImportAllowed(string source, string target)
    {
        if (source == "Trureturing.lean")
        {
            return target.StartsWith("D5/", StringComparison.Ordinal)
                && !target.Contains("/X_Frontier/", StringComparison.Ordinal);
        }

        var sourceParts = source.Split('/');
        var targetParts = target.Split('/');
        if (sourceParts.Length < 3 || targetParts.Length < 3)
        {
            return false;
        }

        var sourceZone = sourceParts[1];
        var targetZone = targetParts[1];
        if (sourceZone == "X_Frontier") return true;
        if (targetZone == "X_Frontier") return false;
        if (IsStratum(sourceZone))
        {
            // Strata build up on the registered-assumption foundation: content that
            // carries a classical theorem via AxiomDebt must import X_Assumptions.
            return (IsStratum(targetZone) && targetZone[1] <= sourceZone[1])
                || targetZone == "X_Assumptions";
        }

        return sourceZone switch
        {
            // X_Assumptions is the foundation (imports only external Mathlib, nothing
            // in-repo); keeping it a sink makes the import partial order acyclic.
            "X_Assumptions" => false,
            "X_Certificates" => IsStratum(targetZone) || targetZone == "X_Assumptions",
            _ => false,
        };
    }

    private static bool IsStratum(string value) => value is "S0" or "S1" or "S2" or "S3" or "S4";

    private static bool IsStatusScope(string path) => path.StartsWith(
        new[] { "D5/", "Blueprint/", "Evidence/", "Library/", "Papers/", "Chronicle/" },
        StringComparison.Ordinal);

    internal static IEnumerable<(RepoPath Path, RepositoryFile File)> FormalFiles(RepositorySnapshot snapshot) =>
        snapshot.Files
            .Where(static item => item.Key.Value.StartsWith("D5/", StringComparison.Ordinal)
                && item.Key.Value.EndsWith(".lean", StringComparison.Ordinal))
            .Select(static item => (item.Key, item.Value));

    internal static bool TryHeader(string text, out HeaderData header)
    {
        var match = HeaderPattern.Match(text);
        if (!match.Success || string.IsNullOrWhiteSpace(match.Groups["digest"].Value))
        {
            header = HeaderData.Empty;
            return false;
        }

        header = new HeaderData(
            match.Groups["gid"].Value.Trim(),
            match.Groups["generality"].Value,
            match.Groups["mirrorB"].Value.Trim(),
            match.Groups["mirrorE"].Value.Trim(),
            match.Groups["anchors"].Value.Split(',', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries));
        return true;
    }

    private static bool MirrorPairAffected(
        RuleEvaluationContext context,
        string sourcePath,
        HeaderData header) =>
        context.IsBaseFactAffected(sourcePath)
        || MirrorPathAffected(context, header.MirrorB, "D5/B/")
        || MirrorPathAffected(context, header.MirrorE, "D5/E/");

    private static bool MirrorPathAffected(
        RuleEvaluationContext context,
        string value,
        string prefix)
    {
        if (!value.StartsWith(prefix, StringComparison.Ordinal)
            || !Gid.TryParse(value, out var gid))
        {
            return false;
        }

        return context.IsBaseFactAffected(gid.Path.Value);
    }

    private static void ValidateMirror(
        string source,
        string label,
        string value,
        string prefix,
        RepositorySnapshot snapshot,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        if (value.StartsWith("none(waiver:", StringComparison.Ordinal) && value.EndsWith(')'))
        {
            if (string.IsNullOrWhiteSpace(value["none(waiver:".Length..^1]))
            {
                findings.Add(new RuleFinding(source, $"{label} waiver has no reason"));
            }

            return;
        }

        if (!value.StartsWith(prefix, StringComparison.Ordinal) || !Gid.TryParse(value, out var gid))
        {
            findings.Add(new RuleFinding(source, $"{label} must be a full GID or explicit waiver"));
            return;
        }

        if (!snapshot.TryGetFile(gid.Path.Value, out _))
        {
            var kind = label == "mirror-E" ? "evidence mirror" : "mirror";
            findings.Add(new RuleFinding(source, $"missing {kind} {gid.Path.Value}"));
        }
    }

    private static HashSet<string> ImportClosure(
        string source,
        IReadOnlyDictionary<string, ImmutableArray<string>> imports)
    {
        var seen = new HashSet<string>(StringComparer.Ordinal);
        var stack = new Stack<string>(imports.GetValueOrDefault(source, ImmutableArray<string>.Empty));
        while (stack.TryPop(out var target))
        {
            if (!seen.Add(target)) continue;
            foreach (var nested in imports.GetValueOrDefault(target, ImmutableArray<string>.Empty))
            {
                stack.Push(nested);
            }
        }

        return seen;
    }

    // SL-019 consumes the repository-wide TASK token grammar. Keep this regex byte-for-byte
    // identical to the retired task-block scanner's production pattern.
    private static readonly Regex TaskTokenPattern = new(
        "TASK\\s+(?<code>D5-T[0-9]{4})",
        RegexOptions.CultureInvariant);

    private static HashSet<string> CollectTaskCodes(RepositorySnapshot snapshot) =>
        CollectTaskCodes(FormalFiles(snapshot).Select(static item => item.File));

    private static HashSet<string> CollectTaskCodes(IEnumerable<RepositoryFile> files)
    {
        var result = new HashSet<string>(StringComparer.Ordinal);
        foreach (var file in files.OrderBy(static item => item.Path.Value, StringComparer.Ordinal))
        {
            foreach (Match match in TaskTokenPattern.Matches(file.Text))
            {
                result.Add(match.Groups["code"].Value);
            }
        }

        return result;
    }

    internal sealed record HeaderData(
        string Gid,
        string Generality,
        string MirrorB,
        string MirrorE,
        string[] Anchors)
    {
        internal static HeaderData Empty { get; } = new(string.Empty, string.Empty, string.Empty, string.Empty, Array.Empty<string>());
    }

}

internal static class StringExtensions
{
    internal static bool StartsWith(
        this string value,
        IEnumerable<string> prefixes,
        StringComparison comparison) =>
        prefixes.Any(prefix => value.StartsWith(prefix, comparison));
}
