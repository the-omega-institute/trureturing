using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;
using System.Text.RegularExpressions;
using StrataLint.Definitions;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record ConservativeCorpusObject(string Root, string BytesBase64);

internal sealed record ConservativeCorpusFile(string Path, string ObjectRoot);

internal sealed record ConservativeCorpusDeclaration(
    string Name,
    string NameKey,
    string Kind,
    [property: JsonPropertyName("type")]
    string TypeRepresentation,
    bool IncludeInStatement,
    ImmutableArray<string> Axioms);

internal sealed record ConservativeCorpusLeanFile(
    string Path,
    ImmutableArray<string> Imports,
    ImmutableArray<ConservativeCorpusDeclaration> Declarations,
    string? Error);

internal sealed record ConservativeCorpusCase(
    string CaseId,
    string CaseRoot,
    ImmutableArray<ConservativeCorpusFile> CurrentFiles,
    ImmutableArray<ConservativeCorpusFile> BaselineFiles,
    ImmutableArray<ConservativeCorpusLeanFile> CurrentLean,
    ImmutableArray<ConservativeCorpusLeanFile> BaselineLean,
    ImmutableArray<string> Changes);

internal sealed record MaterializedConservativeCorpus(
    ImmutableArray<byte> CanonicalBytes,
    string Root,
    ImmutableArray<string> CaseIds);

internal static partial class GoldenCorpusMaterializer
{
    private const string Schema = "stratalint-conservative-corpus-v1";
    private const string AnchorCatalogPath = "Meta/StrataLint/Generated/anchor-catalog.v1.json";
    private const string BackfillPath = "Meta/BACKFILL.yaml";
    private const string GictTheoryPath = "docs/develop/theory/GICT_complete_development_v3_3.md";
    private const string PzgTheoryPath = "docs/develop/theory/PZG_BEDC_kernel_formal_170.md";
    private const string SpecificationPath = "docs/develop/spec/golden-ledger-repo-spec.md";

    internal static MaterializedConservativeCorpus Materialize(string baselineRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(baselineRoot);
        var root = Path.GetFullPath(baselineRoot);
        if (!Directory.Exists(root))
        {
            throw new DirectoryNotFoundException($"baseline root is absent: {root}");
        }

        var objects = new Dictionary<string, ConservativeCorpusObject>(StringComparer.Ordinal);
        var cases = GoldenCorpus.All
            .Select(item => MaterializeCase(root, item, objects))
            .OrderBy(static item => item.CaseId, StringComparer.Ordinal)
            .ToImmutableArray();
        var material = JsonSerializer.SerializeToElement(new
        {
            cases = cases.Select(static item => CanonicalCase(item)),
            objects = objects.Values
                .OrderBy(static item => item.Root, StringComparer.Ordinal)
                .Select(static item => new
                {
                    bytes_base64 = item.BytesBase64,
                    root = item.Root,
                }),
            schema = Schema,
        });
        var bytes = StructuredCanonicalWriter.WriteJson(material);
        return new MaterializedConservativeCorpus(
            bytes,
            ContentRoot(bytes.AsSpan()),
            cases.Select(static item => item.CaseId).ToImmutableArray());
    }

    private static ConservativeCorpusCase MaterializeCase(
        string root,
        GoldenCase source,
        IDictionary<string, ConservativeCorpusObject> objects)
    {
        var state = GoldenFixtureState.Create(root);
        state.NormalizeBackfillTargets();
        state.Apply(source.Name, source.BaselineMutations, baseline: true);
        state.Apply(source.Name, source.BaselineMutations, baseline: false);
        state.Apply(source.Name, source.Mutations, baseline: false);
        var prototype = new ConservativeCorpusCase(
            $"golden:{source.Name}",
            string.Empty,
            Files(state.Files, objects),
            Files(state.Baseline, objects),
            LeanFiles(state.Reports),
            LeanFiles(state.BaselineReports),
            [GoldenCorpus.BlueprintPath]);
        return prototype with { CaseRoot = CaseRoot(prototype) };
    }

    private static ImmutableArray<ConservativeCorpusFile> Files(
        IReadOnlyDictionary<string, string> files,
        IDictionary<string, ConservativeCorpusObject> objects)
    {
        var builder = ImmutableArray.CreateBuilder<ConservativeCorpusFile>(files.Count);
        foreach (var (path, text) in files.OrderBy(static item => item.Key, StringComparer.Ordinal))
        {
            var bytes = new UTF8Encoding(false, true).GetBytes(text);
            var root = ContentRoot(bytes);
            objects.TryAdd(root, new ConservativeCorpusObject(root, Convert.ToBase64String(bytes)));
            builder.Add(new ConservativeCorpusFile(path, root));
        }

        return builder.MoveToImmutable();
    }

    private static ImmutableArray<ConservativeCorpusLeanFile> LeanFiles(
        IReadOnlyDictionary<string, LeanFileReport> reports) =>
        reports.OrderBy(static item => item.Key, StringComparer.Ordinal)
            .Select(static item => new ConservativeCorpusLeanFile(
                item.Key,
                item.Value.Imports.Order(StringComparer.Ordinal).ToImmutableArray(),
                item.Value.Declarations
                    .OrderBy(static declaration => declaration.NameKey, StringComparer.Ordinal)
                    .ThenBy(static declaration => declaration.Kind, StringComparer.Ordinal)
                    .ThenBy(static declaration => declaration.Name, StringComparer.Ordinal)
                    .Select(static declaration => new ConservativeCorpusDeclaration(
                        declaration.Name,
                        declaration.NameKey,
                        declaration.Kind,
                        declaration.TypeRepresentation,
                        declaration.IncludeInStatement,
                        declaration.Axioms.Order(StringComparer.Ordinal).ToImmutableArray()))
                    .ToImmutableArray(),
                item.Value.Error))
            .ToImmutableArray();

    private static object CanonicalCase(ConservativeCorpusCase item, bool includeRoot = true) => new
    {
        baseline_files = item.BaselineFiles.Select(static file => new
        {
            object_root = file.ObjectRoot,
            path = file.Path,
        }),
        baseline_lean = item.BaselineLean.Select(CanonicalLean),
        case_id = item.CaseId,
        case_root = includeRoot ? item.CaseRoot : null,
        changes = item.Changes,
        current_files = item.CurrentFiles.Select(static file => new
        {
            object_root = file.ObjectRoot,
            path = file.Path,
        }),
        current_lean = item.CurrentLean.Select(CanonicalLean),
    };

    private static object CanonicalLean(ConservativeCorpusLeanFile item) => new
    {
        declarations = item.Declarations.Select(static declaration => new
        {
            axioms = declaration.Axioms,
            include_in_statement = declaration.IncludeInStatement,
            kind = declaration.Kind,
            name = declaration.Name,
            name_key = declaration.NameKey,
            type = declaration.TypeRepresentation,
        }),
        error = item.Error,
        imports = item.Imports,
        path = item.Path,
    };

    internal static string ContentRoot(ReadOnlySpan<byte> bytes) =>
        "sha256:" + Convert.ToHexStringLower(SHA256.HashData(bytes));

    internal static string CaseRoot(ConservativeCorpusCase item)
    {
        var bytes = StructuredCanonicalWriter.WriteJson(
            JsonSerializer.SerializeToElement(CanonicalCase(item, includeRoot: false)));
        return ContentRoot(bytes.AsSpan());
    }

    private sealed class GoldenFixtureState
    {
        private GoldenFixtureState(
            string repositoryRoot,
            Dictionary<string, string> files,
            Dictionary<string, string> baseline,
            Dictionary<string, LeanFileReport> reports,
            Dictionary<string, LeanFileReport> baselineReports)
        {
            RepositoryRoot = repositoryRoot;
            Files = files;
            Baseline = baseline;
            Reports = reports;
            BaselineReports = baselineReports;
        }

        private string RepositoryRoot { get; }

        internal Dictionary<string, string> Files { get; }

        internal Dictionary<string, string> Baseline { get; }

        internal Dictionary<string, LeanFileReport> Reports { get; }

        internal Dictionary<string, LeanFileReport> BaselineReports { get; }

        internal static GoldenFixtureState Create(string root)
        {
            var files = new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["Meta/domains.yaml"] = GoldenCorpus.FixtureDomains,
                [BackfillPath] = Read(root, BackfillPath),
                ["Meta/registry.yaml"] = GoldenCorpus.FixtureRegistry,
                [AnchorCatalogPath] = Read(root, AnchorCatalogPath),
                ["Library/queries.yaml"] = "schema_version: 1\nqueries: []\n",
                [GoldenCorpus.RingPath] = GoldenHeader(
                    "D5/S0/Carrier/Ring",
                    Generality.General,
                    "D5/B/S0/Carrier/Ring") + "def goldenRing : Nat := 0\n",
                [GoldenCorpus.BlueprintPath] = "# Golden ring\n",
                [GictTheoryPath] = Read(root, GictTheoryPath),
                [PzgTheoryPath] = Read(root, PzgTheoryPath),
                [SpecificationPath] = RestoreApprovedCanonicalClaim(Read(root, SpecificationPath)),
            };
            var reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            {
                [GoldenCorpus.RingPath] = Report(declarations:
                [
                    new LeanDeclaration(
                        "goldenRing",
                        "def",
                        "Nat",
                        ImmutableArray<string>.Empty),
                ]),
            };
            return new GoldenFixtureState(
                root,
                files,
                new Dictionary<string, string>(files, StringComparer.Ordinal),
                reports,
                new Dictionary<string, LeanFileReport>(reports, StringComparer.Ordinal));
        }

        internal void NormalizeBackfillTargets()
        {
            AddNormalizedBackfillTicketTarget();
            AddNormalizedBackfillCoverageTarget();
            foreach (var files in new[] { Files, Baseline })
            {
                var lines = files[BackfillPath].Split('\n');
                var normalized = new List<string>(lines.Length);
                for (var index = 0; index < lines.Length; index++)
                {
                    var trimmed = lines[index].TrimStart();
                    var indentation = lines[index][..(lines[index].Length - trimmed.Length)];
                    if (trimmed == "coverage_gids:")
                    {
                        normalized.Add(lines[index]);
                        while (index + 1 < lines.Length
                            && lines[index + 1].StartsWith(indentation + "  - ", StringComparison.Ordinal))
                        {
                            index++;
                        }

                        normalized.Add(indentation + "  - D5/S0/Carrier/BackfillTarget");
                    }
                    else if (trimmed.StartsWith("gid: ", StringComparison.Ordinal))
                    {
                        normalized.Add(indentation + "gid: D5/X_Frontier/BackfillTasks");
                    }
                    else if (trimmed.StartsWith("truth: ", StringComparison.Ordinal))
                    {
                        normalized.Add(indentation + "truth: closed");
                    }
                    else
                    {
                        normalized.Add(lines[index]);
                    }
                }

                files[BackfillPath] = string.Join('\n', normalized);
            }
        }

        internal void Apply(
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
                            GoldenHeader(lean.RawGid, ToGenerality(lean.Generality)) + lean.Body);
                        break;
                    case GoldenMutation.Delete delete:
                        files.Remove(delete.Path);
                        reports.Remove(delete.Path);
                        break;
                    case GoldenMutation.AppendLines append:
                        files[append.Path] += string.Concat(Enumerable.Repeat(
                            append.Line + "\n",
                            append.Count));
                        break;
                    case GoldenMutation.AddDomain domain:
                        AddDomain(caseName, files, domain);
                        break;
                    case GoldenMutation.AddTask task:
                        AddTask(caseName, files, reports, task);
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
                            GoldenCorpus.RingPath,
                            GoldenHeader(
                                "D5/S0/Carrier/Ring",
                                Generality.General,
                                "none(waiver:)",
                                "none(waiver:test)")
                            + "def goldenRing : Nat := 0\n");
                        break;
                    case GoldenMutation.EvidenceMirror mirror:
                        ApplyEvidenceMirror(caseName, files, reports, mirror);
                        break;
                    case GoldenMutation.ReplaceBackfill replace:
                        ReplaceBackfill(files, replace.OldValue, replace.NewValue);
                        break;
                    case GoldenMutation.ReplaceFirstBackfillDisposition disposition:
                        ReplaceDisposition(files, disposition.RawGid);
                        break;
                    case GoldenMutation.MutateBackfillAnchor anchor:
                        MutateAnchor(files, anchor.Anchor, anchor.Duplicate);
                        break;
                    default:
                        throw new InvalidOperationException(
                            $"unsupported typed mutation: {mutation.GetType().Name}");
                }
            }
        }

        private void AddNormalizedBackfillTicketTarget()
        {
            const string gid = "D5/X_Frontier/BackfillTasks";
            var path = gid + ".lean";
            Files[path] = GoldenHeader(gid, Generality.Extremal)
                + string.Concat(Enumerable.Range(1, 18).Select(static number =>
                    $"/-- TASK D5-T{number:0000} | 难度:3 | 依赖:就绪 | 尝试:0\n"
                    + "    提示:Fixture task.\n"
                    + "    尸检:none -/\n"
                    + $"def fixtureTask{number:0000} : Unit := ()\n"));
            Reports[path] = Report();
        }

        private void AddNormalizedBackfillCoverageTarget()
        {
            const string gid = "D5/S0/Carrier/BackfillTarget";
            var path = gid + ".lean";
            var text = GoldenHeader(gid, Generality.General) + "def backfillTarget : Unit := ()\n";
            var report = Report(declarations:
            [
                new LeanDeclaration(
                    "backfillTarget",
                    "def",
                    "Unit",
                    ImmutableArray<string>.Empty),
            ]);
            Files[path] = text;
            Baseline[path] = text;
            Reports[path] = report;
            BaselineReports[path] = report;
        }

        private static void AddDomain(
            string caseName,
            IDictionary<string, string> files,
            GoldenMutation.AddDomain domain)
        {
            if (!DomainId.TryCreate(domain.Name, out var domainName))
            {
                throw new InvalidOperationException(
                    $"golden case {caseName} has an invalid domain name: {domain.Name}");
            }

            var lines = files["Meta/domains.yaml"].Split('\n').ToList();
            var insertion = lines.FindIndex(1, line =>
            {
                if (!line.StartsWith("  ", StringComparison.Ordinal)
                    || line.StartsWith("    ", StringComparison.Ordinal)
                    || !line.EndsWith(':'))
                {
                    return false;
                }

                return string.CompareOrdinal(line[2..^1], domainName.Value) > 0;
            });
            if (insertion < 0)
            {
                insertion = lines.Count;
                if (insertion > 0 && lines[^1].Length == 0) insertion--;
            }

            lines.InsertRange(insertion,
            [
                $"  {domainName.Value}:",
                $"    stratum: {domain.Stratum}",
                "    definition: Fixture.",
            ]);
            files["Meta/domains.yaml"] = string.Join('\n', lines);
        }

        private static void AddTask(
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
                && !files[BackfillPath].Contains(
                    $"case_id: {task.RawCaseId}\n",
                    StringComparison.Ordinal))
            {
                files[BackfillPath] +=
                    $"  - case_id: {task.RawCaseId}\n    gid: {task.RawGid}\n";
            }
        }

        private static void WriteGolden(
            string caseName,
            IDictionary<string, string> files,
            IDictionary<string, LeanFileReport> reports,
            string path,
            string content)
        {
            if (!RepoPath.TryCreate(path, out var repoPath))
            {
                throw new InvalidOperationException($"golden case {caseName} has invalid path {path}");
            }

            files[repoPath.Value] = content;
            if (LeanClosureValidator.IsManagedLean(repoPath.Value))
            {
                reports[repoPath.Value] = SemanticReport(caseName, repoPath.Value, content);
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
            foreach (Match match in AxiomRegex().Matches(semantic))
            {
                var name = match.Groups["name"].Value;
                if (match.Groups["modifier"].Value == "private")
                {
                    name = $"_private.{path[..^5].Replace('/', '.')}.0.{name}";
                }
                else
                {
                    var namespaceMatch = NamespaceRegex().Match(semantic);
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

            foreach (Match match in TheoremRegex().Matches(semantic))
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

        private static void ApplyEvidenceMirror(
            string caseName,
            IDictionary<string, string> files,
            IDictionary<string, LeanFileReport> reports,
            GoldenMutation.EvidenceMirror mirror)
        {
            WriteGolden(
                caseName,
                files,
                reports,
                GoldenCorpus.RingPath,
                GoldenHeader(
                    "D5/S0/Carrier/Ring",
                    Generality.General,
                    "D5/B/S0/Carrier/Ring",
                    "D5/E/S0/Carrier/Ring.result--json")
                + "def goldenRing : Nat := 0\n");
            if (mirror.IncludeJson) files["Evidence/D5/S0/Carrier/Ring.result.json"] = "{}\n";
            if (mirror.IncludeYaml)
            {
                files["Evidence/D5/S0/Carrier/Ring.result.yaml"] = "result: duplicate\n";
            }
        }

        private static void ReplaceBackfill(
            IDictionary<string, string> files,
            string oldValue,
            string newValue)
        {
            var text = files[BackfillPath];
            var index = text.IndexOf(oldValue, StringComparison.Ordinal);
            if (index < 0)
            {
                throw new InvalidOperationException($"unknown protected fixture text '{oldValue}'");
            }

            files[BackfillPath] = string.Concat(
                text.AsSpan(0, index),
                newValue,
                text.AsSpan(index + oldValue.Length));
        }

        private static void ReplaceDisposition(IDictionary<string, string> files, string rawGid)
        {
            var lines = files[BackfillPath].Split('\n').ToList();
            var coverage = lines.FindIndex(static line => line.Trim() == "coverage_gids:");
            var index = coverage + 1;
            if (coverage < 0
                || index >= lines.Count
                || !lines[index].TrimStart().StartsWith("- ", StringComparison.Ordinal))
            {
                throw new InvalidOperationException("BACKFILL fixture has no coverage GID");
            }

            var indentation = lines[index][..(lines[index].Length - lines[index].TrimStart().Length)];
            lines[index] = indentation + "- " + rawGid;
            var truth = lines.FindIndex(
                index + 1,
                line => line.TrimStart().StartsWith("truth: ", StringComparison.Ordinal));
            if (truth >= 0)
            {
                var truthIndentation = lines[truth][..(lines[truth].Length - lines[truth].TrimStart().Length)];
                lines[truth] = truthIndentation + "truth: open";
            }

            files[BackfillPath] = string.Join('\n', lines);
        }

        private static void MutateAnchor(
            IDictionary<string, string> files,
            string anchor,
            bool duplicate)
        {
            var lines = files[BackfillPath].Split('\n').ToList();
            var index = lines.FindIndex(line =>
                string.Equals(line.Trim(), $"- atom_id: {anchor}", StringComparison.Ordinal));
            if (index < 0) throw new InvalidOperationException("unknown digestion atom");
            var next = lines.FindIndex(index + 1, line =>
                line.StartsWith("      - atom_id: ", StringComparison.Ordinal)
                || line.StartsWith("  - source_id: ", StringComparison.Ordinal)
                || line == "ticket_index:");
            if (next < 0) next = lines.Count;
            var block = lines.GetRange(index, next - index);
            if (duplicate) lines.InsertRange(next, block);
            else lines.RemoveRange(index, block.Count);
            files[BackfillPath] = string.Join('\n', lines);
        }

        private static string Read(string root, string relativePath) =>
            File.ReadAllText(Path.Combine(root, relativePath), Encoding.UTF8);
    }

    private static Generality ToGenerality(GoldenGenerality generality) => generality switch
    {
        GoldenGenerality.General => Generality.General,
        GoldenGenerality.Instance => Generality.Instance,
        GoldenGenerality.Extremal => Generality.Extremal,
        _ => throw new InvalidOperationException("unknown golden generality"),
    };

    private static LeanFileReport Report(
        IEnumerable<string>? imports = null,
        IEnumerable<LeanDeclaration>? declarations = null) =>
        new(
            (imports ?? Array.Empty<string>()).ToImmutableArray(),
            (declarations ?? Array.Empty<LeanDeclaration>()).ToImmutableArray());

    private static string GoldenHeader(
        string gid,
        Generality generality,
        string mirrorB = "none(waiver:test-fixture)",
        string mirrorE = "none(waiver:test-fixture)") => $"""
        /- GID: {gid}
           generality: {GeneralityCode(generality)}
           mirror-B: {mirrorB}
           mirror-E: {mirrorE}
           anchors: []
           digest: StrataLint fixture. -/
        """;

    private static string GeneralityCode(Generality generality) => generality switch
    {
        Generality.General => "G",
        Generality.Instance => "I",
        Generality.Extremal => "E",
        _ => throw new ArgumentOutOfRangeException(nameof(generality)),
    };

    private static string RestoreApprovedCanonicalClaim(string text)
    {
        const string marker = "**papergen/blueprint 只接受全 GID;跨库引用自带理论坐标。**";
        const string approved = " **M0 admission 精确主张**:给定一个受支持且经人类门控核准的语义 manifest,至多存在一种规范表示与恰一次 admission;不受支持或未核准的 manifest 按 fail-closed 得零次 admission。受 manifest 路由的 JSON/YAML 结构化语义工件现役强制 UTF-8、禁 BOM、对象键字典序、禁行尾空白且末尾恰一 LF;完整 Unicode NFC、默认值与 tag 顺序规范化延后 D5-T0015,故字节规范不得报 full active。";
        if (text.Contains(approved, StringComparison.Ordinal)) return text;
        if (!text.Contains(marker, StringComparison.Ordinal))
        {
            throw new InvalidOperationException(
                "protected spec fixture lacks the approved canonical-claim anchor");
        }

        return text.Replace(marker, marker + approved, StringComparison.Ordinal);
    }

    [GeneratedRegex(
        "(?:(?<modifier>protected|private)\\s+)?axiom\\s+(?<name>[A-Za-z_][A-Za-z0-9_]*)\\s*:\\s*(?<type>[^\\n]+)",
        RegexOptions.CultureInvariant)]
    private static partial Regex AxiomRegex();

    [GeneratedRegex("^namespace\\s+(?<name>\\S+)", RegexOptions.Multiline)]
    private static partial Regex NamespaceRegex();

    [GeneratedRegex(
        "theorem\\s+(?<name>[A-Za-z_][A-Za-z0-9_]*)\\s*:\\s*(?<type>.*?)\\s*:=",
        RegexOptions.Singleline | RegexOptions.CultureInvariant)]
    private static partial Regex TheoremRegex();
}
