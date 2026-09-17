using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using Trureturing.Truth;
using File = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

internal sealed class InformationTemplateHistoryFixture : IDisposable, IInformationTemplateHistoryRepository, IGitProcessRunner
{
    internal readonly TemporaryDirectory Scratch = new();
    internal string Head => InformationTemplateHistoryPlanTests.Base;
    internal string Seed => InformationTemplateHistoryPlanTests.Seed;
    internal string Plan => Path.Combine(Scratch.Path, "plan.json");
    internal string Work => Path.Combine(Scratch.Path, "private work");
    internal string Output => Path.Combine(Scratch.Path, "bundle");
    internal readonly Dictionary<string, string> Candidate;
    internal readonly Dictionary<string, string> Historical;
    internal int CandidateReads, HistoricalReads, Productions;
    internal bool FailProducer, TimeoutProducer;
    internal string? ProducerCwd;
    internal IReadOnlyList<string> ProducerArguments = [];
    internal RepositorySnapshot CandidateSnapshot => Decode(Candidate);
    public string CurrentRevision => Head;

    internal InformationTemplateHistoryFixture()
    {
        Candidate = new(StringComparer.Ordinal)
        {
            ["Trureturing.lean"] = "-- candidate root\n",
            ["D5/S0/Carrier/History.lean"] = "-- candidate content\n",
            ["D5/S0/Carrier/Candidate.lean"] = "-- candidate addition\n",
            ["Golden/Frozen/state/probe.lean.json"] = "candidate state",
            ["lean-toolchain"] = "leanprover/lean4:v4.33.0\n",
            ["lake-manifest.json"] = "{\"packages\":[]}",
            ["lakefile.toml"] = "name = \"fixture\"\n",
            [".gitignore"] = ".lake/\n**/bin/\n**/obj/\n",
            ["tools/lean-inspector/inspect.sh"] = "#!/bin/sh\n# candidate inspector\n",
            ["tools/StrataLint.Cli/Fixture.cs"] = "candidate runtime",
            ["tools/StrataLint.Scribe/Fixture.cs"] = "candidate runtime",
            [InformationTemplateDebtStore.ActivationPath] = DeclaredTemplateReviewTests.Text(
                InformationTemplateDebtStore.WriteActivation(new(Seed, false))),
            ["lean-report-inputs.json"] = """
                {"schema_version":1,"report_semantic_version":6,
                 "report_modules":{"include":[{"pattern":"Trureturing.lean","optional":false},{"pattern":"D5/**/*.lean","optional":true}],"exclude":[]},
                 "inspector_sources":{"include":[],"exclude":[]},
                 "dependency_sources":{"include":[],"exclude":[]},
                 "config_inputs":{"include":[{"pattern":"lean-toolchain","optional":false},{"pattern":"lake-manifest.json","optional":false},{"pattern":"lakefile.toml","optional":false},{"pattern":"lakefile.lean","optional":true}],"exclude":[]},
                 "producer_scopes":{"lean-report":{"include":[{"pattern":"lean-report-inputs.json","optional":false},{"pattern":"tools/**","optional":false},{"pattern":".gitignore","optional":false},{"pattern":"Meta/lean-report.toml","optional":true}],"exclude":["**/bin/**","**/obj/**","**/.lake/**"]},"scribe-content":{"include":[],"exclude":[]}}}
                """,
        };
        Historical = new(Candidate, StringComparer.Ordinal)
        {
            ["Trureturing.lean"] = "-- historical root\n",
            ["D5/S0/Carrier/History.lean"] = "-- historical content\n",
            ["Golden/Frozen/state/probe.lean.json"] = "historical state",
            ["tools/lean-inspector/inspect.sh"] = "historical executable must never run",
            ["tools/StrataLint.Scribe/Fixture.cs"] = "historical runtime must never run",
            ["Meta/lean-report.toml"] = "historical deleted config",
        };
        Historical.Remove("D5/S0/Carrier/Candidate.lean");
        Directory.CreateDirectory(Path.Combine(Scratch.Path, "candidate"));
    }

    internal static RawRepositorySnapshot Raw(Dictionary<string, string> files) =>
        RawRepositorySnapshot.Create(files.Select(p => RawRepositoryEntry.FromText(p.Key, p.Value)));
    internal static RepositorySnapshot Decode(Dictionary<string, string> files) =>
        ((SnapshotDecodeOutcome.Decoded)SnapshotDecoder.Decode(Raw(files))).Snapshot;
    public string ResolveBase(string? revision) => revision is null || revision == Head ? Head
        : throw new FormatException("fixture base unavailable");
    public RawRepositorySnapshot ReadPredicate(string? revision) => Raw(Candidate.Where(p =>
        p.Key.StartsWith(InformationTemplateDebtStore.Root, StringComparison.Ordinal)).ToDictionary());
    public RawRepositorySnapshot ReadCandidate() { CandidateReads++; return Raw(Candidate); }
    public RawRepositorySnapshot ReadHistorical(string revision)
    {
        HistoricalReads++;
        return revision == Seed ? Raw(Historical) : revision == Head ? Raw(Candidate)
            : throw new FormatException("fixture missing historical object");
    }
    internal CommandResult Command(params string[] arguments) => InformationTemplateHistoryCommand.Run(
        Path.Combine(Scratch.Path, "candidate"), this,
        arguments[0] is "produce" or "adopt" && !arguments.Contains("--cache-root", StringComparer.Ordinal)
            ? [.. arguments, "--cache-root", Path.Combine(Scratch.Path, "cache")] : arguments, this, TimeProvider.System);
    internal void SeedPlan()
    {
        var result = Command("plan", "--protected-base", Head, "--purpose", "seed", "--output", Plan,
            "--os", "Linux", "--arch", "ARM64");
        Assert.True(result.Success, "[FAIL] seed plan: " + result.Error);
    }
    internal CommandResult Produce() => Command("produce", "--plan", Plan, "--revision", Seed,
        "--work", Work, "--output", Output, "--cache-root", Path.Combine(Scratch.Path, "cache"));
    internal CommandResult Validate() => Command("validate", "--plan", Plan, "--revision", Seed, "--bundle", Output);

    public ProcessOutput Run(string fileName, IReadOnlyList<string> arguments, string workingDirectory,
        TimeSpan timeout, int maximumOutputBytes = GitRepositoryGateway.DefaultGitOutputBytes,
        ReadOnlyMemory<byte> standardInput = default)
    {
        if (fileName == "git") return new ProductionGitProcessRunner().Run(fileName, arguments,
            workingDirectory, timeout, maximumOutputBytes, standardInput);
        Productions++;
        ProducerCwd = workingDirectory;
        ProducerArguments = arguments;
        if (TimeoutProducer) throw new TimeoutException("fixture timeout");
        if (FailProducer) return new(19, [], Encoding.UTF8.GetBytes("fixture inspector failed"));
        Assert.Equal("/bin/bash", fileName);
        Assert.Equal("--repository", arguments[1]);
        Assert.Equal(workingDirectory, arguments[2]);
        Assert.Equal("--output", arguments[3]);
        WriteBundle(arguments[4], InformationTemplateEvidence.HistoricalInputs(Decode(Historical), CandidateSnapshot));
        return new(0, Encoding.UTF8.GetBytes("fixture inspector completed\n"), []);
    }

    internal static void WriteBundle(string path, RepositorySnapshot inputs)
    {
        var sources = inputs.Files.Values.Where(f => f.Path.Value == "Trureturing.lean"
            || f.Path.Value.StartsWith("D5/", StringComparison.Ordinal) && f.Path.Value.EndsWith(".lean", StringComparison.Ordinal))
            .OrderBy(f => f.Path.Value, StringComparer.Ordinal).ToArray();
        var configuration = new[] { "lake-manifest.json", "lakefile.toml", "lean-toolchain" };
        var evidenceInputs = sources.Select(f => f.Path.Value).Concat(new[] { "lean-report-inputs.json", "lean-toolchain", "lake-manifest.json" })
            .Order(StringComparer.Ordinal).Select(p => new { path = p, sha256 = Hash(inputs.Files[RepoPath.CreateKnown(p)].RawBytes.AsSpan()) }).ToArray();
        var report = LeanAxiomReport.Create(sources.ToDictionary(f => f.Path.Value, f => new LeanFileReport([], [])
        {
            InformationTemplates = InformationTemplateEvidence.Read(JsonSerializer.SerializeToElement(new
            {
                schema_version = 1, compatibility_version = 6, inputs = evidenceInputs,
                inventory = Array.Empty<object>(), registered = Array.Empty<object>(), records = Array.Empty<object>(),
            }), f.Path.Value, inputs),
        }));
        RawLeanReportArtifact.WriteFile(path, inputs, report);
        var sha = Hash(File.ReadAllBytes(path));
        string InputHash(IEnumerable<string> paths) => Hash(Encoding.UTF8.GetBytes(string.Concat(paths.Select(p =>
            Hash(inputs.Files[RepoPath.CreateKnown(p)].RawBytes.AsSpan()) + "  " + p + "\n"))));
        var sourcesSha = InputHash(sources.Select(f => f.Path.Value));
        var configSha = InputHash(configuration);
        var compatibility = Hash(Encoding.UTF8.GetBytes("schema=stratalint-lean-report-compatibility\nversion=6\n"));
        var common = $"repository_inspector_sha256={compatibility}\nlean_sources_sha256={sourcesSha}\nlean_config_sha256={configSha}\n";
        var repository = Hash(Encoding.UTF8.GetBytes("schema=stratalint-lean-report-repository-input-v1\n" + common));
        var input = Hash(Encoding.UTF8.GetBytes($"schema=stratalint-lean-report-input-v1\nproducer_sha256={compatibility}\n" + common));
        File.WriteAllText(path + ".sha256", sha + "  " + Path.GetFileName(path) + "\n");
        File.WriteAllText(path + ".input.attestation", "schema=stratalint-lean-report-input-attestation-v1\n"
            + $"repository_input_sha256={repository}\nproducer_sha256={compatibility}\nreport_sha256={sha}\n");
        using var doc = JsonDocument.Parse(File.ReadAllBytes(path));
        var origins = doc.RootElement.GetProperty("modules").EnumerateArray().ToDictionary(row => row.GetProperty("module").GetString()!, row => new
        {
            module = row.GetProperty("module").GetString(),
            report_sha256 = Hash(StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(new
                { schema = RawLeanReportArtifact.Schema, modules = new[] { row } })).AsSpan()),
            compatibility_sha256 = compatibility, producer_sources_sha256 = new string('e', 64),
            inspector_executable_sha256 = new string('f', 64), input_sources = new Dictionary<string, string>
                { [row.GetProperty("source_path").GetString()!] = row.GetProperty("source_sha256").GetString()![7..] },
        });
        File.WriteAllText(path + ".provenance.json", JsonSerializer.Serialize(new
        {
            schema = "stratalint-lean-report-provenance-v2", side = "candidate", source_side = "candidate", mode = "produced",
            input_address = "sha256:" + input, producer_sha256 = compatibility, repository_inspector_sha256 = compatibility,
            lean_sources_sha256 = sourcesSha, lean_config_sha256 = configSha, report_sha256 = sha, module_origins = origins,
        }) + "\n");
    }
    private static string Hash(ReadOnlySpan<byte> bytes) => InformationTemplateJson.Sha256(bytes);
    public void Dispose() => Scratch.Dispose();
}
