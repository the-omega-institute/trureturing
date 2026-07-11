using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class FullPythonCorpusCompatibilityTests
{
    private static void Write(
        string caseName,
        IDictionary<string, string> files,
        IDictionary<string, LeanFileReport> reports,
        string path,
        string content)
    {
        files[path] = content;
        if (LeanClosureValidator.IsManagedLean(path))
        {
            reports[path] = SemanticReport(caseName, path, content);
        }
    }

    private static LeanFileReport SemanticReport(string caseName, string path, string content)
    {
        if (caseName == "managed-early-exit-hides-axiom")
        {
            return new LeanFileReport(
                ImmutableArray<string>.Empty,
                ImmutableArray<LeanDeclaration>.Empty,
                "compiler exited successfully without complete module artifacts");
        }

        if (caseName == "hearts-baseline-inspection-fails" && content.Contains(": :=", StringComparison.Ordinal))
        {
            return new LeanFileReport(
                ImmutableArray<string>.Empty,
                ImmutableArray<LeanDeclaration>.Empty,
                "compiler rejected malformed Hearts fixture");
        }

        var semantic = Regex.Replace(content, "/-.*?-/", string.Empty, RegexOptions.Singleline);
        var imports = Regex.Matches(semantic, "^\\s*import\\s+(?<module>\\S+)", RegexOptions.Multiline)
            .Select(static match => match.Groups["module"].Value.Replace("«D5»", "D5", StringComparison.Ordinal))
            .ToImmutableArray();
        var declarations = ImmutableArray.CreateBuilder<LeanDeclaration>();
        foreach (Match match in Regex.Matches(
            semantic,
            "(?:(?<modifier>protected|private)\\s+)?axiom\\s+(?<name>[A-Za-z_][A-Za-z0-9_]*)\\s*:\\s*(?<type>[^\\n]+)",
            RegexOptions.CultureInvariant))
        {
            var name = match.Groups["name"].Value;
            if (match.Groups["modifier"].Value == "private")
            {
                name = $"_private.{path[..^5].Replace('/', '.')}.0.{name}";
            }
            else
            {
                var namespaceMatch = Regex.Match(semantic, "^namespace\\s+(?<name>\\S+)", RegexOptions.Multiline);
                if (namespaceMatch.Success)
                {
                    name = namespaceMatch.Groups["name"].Value + "." + name;
                }
            }

            declarations.Add(new LeanDeclaration(
                name,
                "axiom",
                match.Groups["type"].Value.Trim(),
                ImmutableArray.Create(name)));
        }

        foreach (Match match in Regex.Matches(
            semantic,
            "theorem\\s+(?<name>[A-Za-z_][A-Za-z0-9_]*)\\s*:\\s*(?<type>.*?)\\s*:=",
            RegexOptions.Singleline | RegexOptions.CultureInvariant))
        {
            var axioms = semantic.Contains("registeredDebt", StringComparison.Ordinal)
                ? ImmutableArray.Create("registeredDebt")
                : match.Value.Contains("sorry", StringComparison.Ordinal)
                    || semantic[(match.Index + match.Length)..].Contains("sorry", StringComparison.Ordinal)
                        ? ImmutableArray.Create("sorryAx")
                        : ImmutableArray<string>.Empty;
            declarations.Add(new LeanDeclaration(
                match.Groups["name"].Value,
                "theorem",
                match.Groups["type"].Value.Trim(),
                axioms));
        }

        return new LeanFileReport(imports, declarations.ToImmutable());
    }

    private static RuleEvaluationContext BuildContext(RuleFixture fixture)
    {
        var current = Decode(fixture.Files);
        var baseline = Decode(fixture.Baseline);
        var registry = Assert.IsType<RegistryLoadOutcome.Accepted>(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(fixture.Files["Meta/domains.yaml"])));
        var meta = Assert.IsType<BootstrapOutcome.Clear>(
            BootstrapGate.Evaluate(RawChangeSet.Create(new[] { RuleFixture.BlueprintPath })));
        return RuleEvaluationContext.Create(
            current,
            baseline,
            registry.Policy,
            AcceptedLeanClosure.Create(LeanAxiomReport.Create(fixture.Reports)),
            AcceptedLeanClosure.Create(LeanAxiomReport.Create(fixture.BaselineReports)),
            RawChangeSet.Create(new[] { RuleFixture.BlueprintPath }),
            meta.Capability);
    }

    private static RepositorySnapshot Decode(IReadOnlyDictionary<string, string> files)
    {
        var raw = RawRepositorySnapshot.Create(files.Select(
            static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

    private static void EvidenceMirror(
        string caseName,
        IDictionary<string, string> files,
        IDictionary<string, LeanFileReport> reports,
        bool includeJson,
        bool includeYaml)
    {
        Write(
            caseName,
            files,
            reports,
            RuleFixture.RingPath,
            Header(
                "D5/S0/Carrier/Ring",
                "G",
                "D5/B/S0/Carrier/Ring",
                "D5/E/S0/Carrier/Ring.result--json")
            + "def goldenRing : Nat := 0\n");
        if (includeJson) files["Evidence/D5/S0/Carrier/Ring.result.json"] = "{}\n";
        if (includeYaml) files["Evidence/D5/S0/Carrier/Ring.result.yaml"] = "result: duplicate\n";
    }

    private static string Header(
        string gid,
        string generality,
        string mirrorB = "none(waiver:test-fixture)",
        string mirrorE = "none(waiver:test-fixture)") => $"""
        /- GID: {gid}
           generality: {generality}
           mirror-B: {mirrorB}
           mirror-E: {mirrorE}
           anchors: []
           digest: StrataLint fixture. -/
        """;

    private static void NormalizeBackfillTargets(RuleFixture fixture)
    {
        fixture.AddNormalizedBackfillTicketTarget();
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            var lines = files["Meta/BACKFILL.yaml"].Split('\n');
            for (var index = 0; index < lines.Length; index++)
            {
                var trimmed = lines[index].TrimStart();
                var indentation = lines[index][..(lines[index].Length - trimmed.Length)];
                if (trimmed.StartsWith("disposition: ", StringComparison.Ordinal))
                {
                    lines[index] = indentation + "disposition: D5/S0/Carrier/Ring";
                }
                else if (trimmed.StartsWith("gid: ", StringComparison.Ordinal))
                {
                    lines[index] = indentation + "gid: D5/X_Frontier/BackfillTasks";
                }
            }

            files["Meta/BACKFILL.yaml"] = string.Join('\n', lines);
        }
    }

    private static void ReplaceOnce(IDictionary<string, string> files, string oldValue, string newValue)
    {
        var text = files["Meta/BACKFILL.yaml"];
        var index = text.IndexOf(oldValue, StringComparison.Ordinal);
        if (index < 0) throw new InvalidOperationException($"unknown protected fixture text '{oldValue}'");
        files["Meta/BACKFILL.yaml"] = string.Concat(
            text.AsSpan(0, index),
            newValue,
            text.AsSpan(index + oldValue.Length));
    }

    private static void ReplaceFirstDisposition(IDictionary<string, string> files, string disposition)
    {
        var lines = files["Meta/BACKFILL.yaml"].Split('\n').ToList();
        var index = lines.FindIndex(static line => line.TrimStart().StartsWith("disposition: ", StringComparison.Ordinal));
        if (index < 0) throw new InvalidOperationException("BACKFILL fixture has no disposition");
        var indentation = lines[index][..(lines[index].Length - lines[index].TrimStart().Length)];
        lines[index] = indentation + "disposition: " + disposition;
        files["Meta/BACKFILL.yaml"] = string.Join('\n', lines);
    }

    private static void MutateAnchor(IDictionary<string, string> files, string anchor, bool duplicate)
    {
        var lines = files["Meta/BACKFILL.yaml"].Split('\n').ToList();
        var index = lines.FindIndex(line => string.Equals(line.Trim(), $"- anchor: {anchor}", StringComparison.Ordinal));
        if (index < 0 || index + 2 > lines.Count) throw new InvalidOperationException("unknown protected anchor");
        var block = lines.GetRange(index, 2);
        if (duplicate) lines.InsertRange(index + 2, block);
        else lines.RemoveRange(index, 2);
        files["Meta/BACKFILL.yaml"] = string.Join('\n', lines);
    }
}
