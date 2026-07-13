using System.Collections.Immutable;
using System.Text;
using System.Text.RegularExpressions;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal sealed partial class RuleFixture
{
    internal void ApplyGoldenMutations(
        string caseName,
        IReadOnlyList<GoldenMutation> mutations,
        bool baseline)
    {
        var files = baseline ? Baseline : Files;
        var reports = baseline ? BaselineReports : Reports;
        foreach (var mutation in mutations)
        {
            switch (mutation)
            {
                case GoldenMutation.Write write:
                    WriteGolden(caseName, files, reports, write.Path, write.Content);
                    break;
                case GoldenMutation.WriteParts write:
                    WriteGolden(caseName, files, reports, write.Path, string.Concat(write.Parts));
                    break;
                case GoldenMutation.Lean lean:
                    WriteGolden(
                        caseName,
                        files,
                        reports,
                        lean.Path,
                        GoldenHeader(lean.RawGid, lean.Generality) + lean.Body);
                    break;
                case GoldenMutation.Delete delete:
                    files.Remove(delete.Path.Value);
                    reports.Remove(delete.Path.Value);
                    break;
                case GoldenMutation.AppendLines append:
                    files[append.Path.Value] += string.Concat(Enumerable.Repeat(
                        append.Line + "\n",
                        append.Count));
                    break;
                case GoldenMutation.AddDomain domain:
                    files["Meta/domains.yaml"] += $"  {domain.Name.Value}:\n"
                        + $"    stratum: {domain.Stratum}\n"
                        + "    definition: Fixture.\n";
                    break;
                case GoldenMutation.AddTask task:
                    AddGoldenTask(caseName, files, reports, task);
                    break;
                case GoldenMutation.PopulateDirectory:
                    for (var index = 0; index < 12; index++)
                    {
                        files[$"Blueprint/D5/S0/Carrier/Extra{index:00}.md"] = "fixture\n";
                    }

                    break;
                case GoldenMutation.EmptyMirrorWaiver:
                    WriteGolden(
                        caseName,
                        files,
                        reports,
                        RepoPath.CreateKnown(RingPath),
                        GoldenHeader(
                            "D5/S0/Carrier/Ring",
                            Generality.General,
                            "none(waiver:)",
                            "none(waiver:test)")
                        + "def goldenRing : Nat := 0\n");
                    break;
                case GoldenMutation.EvidenceMirror mirror:
                    ApplyGoldenEvidenceMirror(caseName, files, reports, mirror);
                    break;
                case GoldenMutation.ReplaceBackfill replace:
                    ReplaceGoldenBackfill(files, replace.OldValue, replace.NewValue);
                    break;
                case GoldenMutation.ReplaceFirstBackfillDisposition disposition:
                    ReplaceGoldenDisposition(files, disposition.RawGid);
                    break;
                case GoldenMutation.MutateBackfillAnchor anchor:
                    MutateGoldenAnchor(files, anchor.Anchor, anchor.Duplicate);
                    break;
                default:
                    throw new InvalidOperationException($"unsupported typed mutation: {mutation.GetType().Name}");
            }
        }
    }

    internal RuleEvaluationContext BuildGoldenContext()
    {
        var current = Decode(Files);
        var baseline = Decode(Baseline);
        var registry = Assert.IsType<RegistryLoadOutcome.Accepted>(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(Files["Meta/domains.yaml"])));
        var meta = Assert.IsType<BootstrapOutcome.Clear>(
            BootstrapGate.Evaluate(RawChangeSet.Create(new[] { BlueprintPath })));
        return RuleEvaluationContext.Create(
            current,
            baseline,
            registry.Policy,
            AcceptedLeanClosure.Create(LeanAxiomReport.Create(Reports)),
            AcceptedLeanClosure.Create(LeanAxiomReport.Create(BaselineReports)),
            RawChangeSet.Create(new[] { BlueprintPath }),
            meta.Capability);
    }

    internal void NormalizeGoldenBackfillTargets()
    {
        AddNormalizedBackfillTicketTarget();
        foreach (var files in new[] { Files, Baseline })
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

    private static void AddGoldenTask(
        string caseName,
        IDictionary<string, string> files,
        IDictionary<string, LeanFileReport> reports,
        GoldenMutation.AddTask task)
    {
        WriteGolden(
            caseName,
            files,
            reports,
            task.Path,
            GoldenHeader(task.RawGid, Generality.Extremal)
            + $"/-- TASK {task.RawCaseId} | 难度:3 | 依赖:就绪 | 尝试:0\n"
            + "    提示:Fixture task.\n"
            + "    尸检:none -/\n"
            + "def fixtureTask : Unit := ()\n");
        if (task.RawCaseId.StartsWith("D5-T", StringComparison.Ordinal)
            && caseName is not ("frontier-task-missing-ticket-index" or "retired-task-code")
            && !files["Meta/BACKFILL.yaml"].Contains(
                $"case_id: {task.RawCaseId}\n",
                StringComparison.Ordinal))
        {
            files["Meta/BACKFILL.yaml"] +=
                $"  - case_id: {task.RawCaseId}\n    gid: {task.RawGid}\n";
        }
    }

    private static void WriteGolden(
        string caseName,
        IDictionary<string, string> files,
        IDictionary<string, LeanFileReport> reports,
        RepoPath path,
        string content)
    {
        files[path.Value] = content;
        if (LeanClosureValidator.IsManagedLean(path.Value))
        {
            reports[path.Value] = GoldenSemanticReport(caseName, path.Value, content);
        }
    }

    private static LeanFileReport GoldenSemanticReport(string caseName, string path, string content)
    {
        if (caseName == "managed-early-exit-hides-axiom")
        {
            return new LeanFileReport(
                ImmutableArray<string>.Empty,
                ImmutableArray<LeanDeclaration>.Empty,
                "compiler exited successfully without complete module artifacts");
        }

        if (caseName == "hearts-baseline-inspection-fails"
            && content.Contains(": :=", StringComparison.Ordinal))
        {
            return new LeanFileReport(
                ImmutableArray<string>.Empty,
                ImmutableArray<LeanDeclaration>.Empty,
                "compiler rejected malformed Hearts fixture");
        }

        var semantic = Regex.Replace(content, "/-.*?-/", string.Empty, RegexOptions.Singleline);
        var imports = Regex.Matches(semantic, "^\\s*import\\s+(?<module>\\S+)", RegexOptions.Multiline)
            .Select(static match => match.Groups["module"].Value.Replace(
                "«D5»",
                "D5",
                StringComparison.Ordinal))
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

    private static void ApplyGoldenEvidenceMirror(
        string caseName,
        IDictionary<string, string> files,
        IDictionary<string, LeanFileReport> reports,
        GoldenMutation.EvidenceMirror mirror)
    {
        WriteGolden(
            caseName,
            files,
            reports,
            RepoPath.CreateKnown(RingPath),
            GoldenHeader(
                "D5/S0/Carrier/Ring",
                Generality.General,
                "D5/B/S0/Carrier/Ring",
                "D5/E/S0/Carrier/Ring.result--json")
            + "def goldenRing : Nat := 0\n");
        if (mirror.IncludeJson)
        {
            files["Evidence/D5/S0/Carrier/Ring.result.json"] = "{}\n";
        }

        if (mirror.IncludeYaml)
        {
            files["Evidence/D5/S0/Carrier/Ring.result.yaml"] = "result: duplicate\n";
        }
    }

    private static string GoldenHeader(
        string gid,
        Generality generality,
        string mirrorB = "none(waiver:test-fixture)",
        string mirrorE = "none(waiver:test-fixture)") => $"""
        /- GID: {gid}
           generality: {GoldenGenerality(generality)}
           mirror-B: {mirrorB}
           mirror-E: {mirrorE}
           anchors: []
           digest: StrataLint fixture. -/
        """;

    private static string GoldenGenerality(Generality generality) => generality switch
    {
        Generality.General => "G",
        Generality.Instance => "I",
        Generality.Extremal => "E",
        _ => throw new ArgumentOutOfRangeException(nameof(generality)),
    };

    private static void ReplaceGoldenBackfill(
        IDictionary<string, string> files,
        string oldValue,
        string newValue)
    {
        var text = files["Meta/BACKFILL.yaml"];
        var index = text.IndexOf(oldValue, StringComparison.Ordinal);
        if (index < 0)
        {
            throw new InvalidOperationException($"unknown protected fixture text '{oldValue}'");
        }

        files["Meta/BACKFILL.yaml"] = string.Concat(
            text.AsSpan(0, index),
            newValue,
            text.AsSpan(index + oldValue.Length));
    }

    private static void ReplaceGoldenDisposition(IDictionary<string, string> files, string rawGid)
    {
        var lines = files["Meta/BACKFILL.yaml"].Split('\n').ToList();
        var index = lines.FindIndex(static line =>
            line.TrimStart().StartsWith("disposition: ", StringComparison.Ordinal));
        if (index < 0)
        {
            throw new InvalidOperationException("BACKFILL fixture has no disposition");
        }

        var indentation = lines[index][..(lines[index].Length - lines[index].TrimStart().Length)];
        lines[index] = indentation + "disposition: " + rawGid;
        files["Meta/BACKFILL.yaml"] = string.Join('\n', lines);
    }

    private static void MutateGoldenAnchor(
        IDictionary<string, string> files,
        string anchor,
        bool duplicate)
    {
        var lines = files["Meta/BACKFILL.yaml"].Split('\n').ToList();
        var index = lines.FindIndex(line =>
            string.Equals(line.Trim(), $"- anchor: {anchor}", StringComparison.Ordinal));
        if (index < 0 || index + 2 > lines.Count)
        {
            throw new InvalidOperationException("unknown protected anchor");
        }

        var block = lines.GetRange(index, 2);
        if (duplicate)
        {
            lines.InsertRange(index + 2, block);
        }
        else
        {
            lines.RemoveRange(index, 2);
        }

        files["Meta/BACKFILL.yaml"] = string.Join('\n', lines);
    }
}
