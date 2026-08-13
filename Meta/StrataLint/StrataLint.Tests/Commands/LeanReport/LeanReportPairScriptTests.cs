using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Lean report environment")]
public sealed class LeanReportPairScriptTests
{
    private const string InputHelperPath = "Meta/StrataLint/scripts/report/lean-report-input.sh";
    private const string MergeCommandPath = "Meta/StrataLint/StrataLint.Cli/Commands/LeanReport/LeanReportMergeCommand.cs";
    private const string RawReportPath = "Meta/StrataLint/StrataLint.Engine/Snapshot/RawLeanReportArtifact.cs";
    private const string CanonicalWriterPath = "Meta/StrataLint/StrataLint.Engine/Snapshot/StructuredCanonicalWriter.cs";
    private const string ScribeProgramPath = "Meta/StrataLint/StrataLint.Scribe/ScribeProgram.cs";
    private static readonly string CliProjectPath = string.Join(
        '/', "Meta", "StrataLint", "StrataLint.Cli", "StrataLint.Cli.csproj");
    private static readonly string EngineProjectPath = string.Join(
        '/', "Meta", "StrataLint", "StrataLint.Engine", "StrataLint.Engine.csproj");
    [Fact]
    public void SingleProductionWritesOneVerifiedCandidateBundle()
    {
        using var fixture = new LeanReportPairFixture();

        var result = fixture.Run();

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.Equal(1, fixture.ProducerInvocationCount);
        using var candidate = fixture.ReadCandidateProvenance();
        Assert.Equal("candidate", candidate.RootElement.GetProperty("side").GetString());
        Assert.Equal("produced", candidate.RootElement.GetProperty("mode").GetString());
        Assert.Equal("candidate", candidate.RootElement.GetProperty("source_side").GetString());
        Assert.Contains(
            "LEAN_REPORT_PROVENANCE side=candidate mode=produced",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
    }

    [Fact]
    public void InvokedProducerBytesParticipateInTheInputAddress()
    {
        using var fixture = new LeanReportPairFixture();
        Assert.Equal(0, fixture.Run().ExitCode);
        using var first = fixture.ReadCandidateProvenance();
        var firstAddress = first.RootElement.GetProperty("input_address").GetString();

        fixture.AppendProducerComment();
        var secondRun = fixture.Run();
        Assert.True(
            secondRun.ExitCode == 0,
            Encoding.UTF8.GetString(secondRun.StandardError));
        using var second = fixture.ReadCandidateProvenance();

        Assert.Equal(2, fixture.ProducerInvocationCount);
        Assert.NotEqual(firstAddress, second.RootElement.GetProperty("input_address").GetString());
    }

    [Fact]
    public void ProductionWritesMeasurementsToCallerHeldLog()
    {
        using var fixture = new LeanReportPairFixture();

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        var metrics = fixture.ReadMetrics();
        var metric = Assert.Single(metrics);
        Assert.Equal("resource", metric.GetProperty("kind").GetString());
        Assert.Equal("lean-producer", metric.GetProperty("role").GetString());
    }

    [Fact]
    public void PairScriptPinsPerModuleReuseOff()
    {
        var script = File.ReadAllText(Path.Combine(
            FindRepositoryRoot(), "Meta", "StrataLint", "scripts", "lean-report-pair.sh"));

        Assert.Contains("Per-module reuse is disabled", script, StringComparison.Ordinal);
        Assert.DoesNotContain("--module-cache-report", script, StringComparison.Ordinal);
        Assert.DoesNotContain("--module-cache-manifest", script, StringComparison.Ordinal);
        Assert.DoesNotContain("--modules-file", script, StringComparison.Ordinal);
    }

    [Fact]
    public void ManifestAcceptsABundleProducedByThePairScript()
    {
        using var fixture = new LeanReportPairFixture();
        Assert.Equal(0, fixture.Run().ExitCode);

        var result = fixture.VerifyCandidateManifest();

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "CLAUDE.md"))) return current.FullName;
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }

    private sealed class LeanReportPairFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        private readonly string candidateRoot;
        private readonly string artifacts;
        private readonly string producerDirectory;
        private readonly string producer;
        private readonly string invocationCount;
        private readonly string candidateReport;
        private readonly string metricsLog;

        internal LeanReportPairFixture()
        {
            candidateRoot = Path.Combine(temporary.Path, "candidate");
            artifacts = Path.Combine(temporary.Path, "reports");
            producerDirectory = Path.Combine(temporary.Path, "producer");
            producer = Path.Combine(producerDirectory, "inspect.sh");
            invocationCount = Path.Combine(producerDirectory, "invocations.txt");
            candidateReport = Path.Combine(artifacts, "candidate.json");
            metricsLog = Path.Combine(temporary.Path, "measurements.jsonl");
            InitializeRepository(candidateRoot);
            Directory.CreateDirectory(artifacts);
            Directory.CreateDirectory(producerDirectory);
            File.WriteAllText(
                Path.Combine(producerDirectory, "Inspector.lean"),
                "def producerFixture : True := by trivial\n",
                new UTF8Encoding(false));
            File.WriteAllText(producer, FakeProducer, new UTF8Encoding(false));
            File.WriteAllText(Path.Combine(candidateRoot, "Meta", "StrataLint", "lean-inspector", "inspect.sh"), FakeProducer, new UTF8Encoding(false));
            File.WriteAllText(
                Path.Combine(candidateRoot, "Meta", "StrataLint", "lean-inspector", "Inspector.lean"),
                "def producerFixture : True := by trivial\n",
                new UTF8Encoding(false));
            var chmod = BoundedProcessRunner.Run(
                "chmod",
                ["+x", producer],
                temporary.Path,
                TimeSpan.FromSeconds(30),
                4096);
            Assert.Equal(0, chmod.ExitCode);
        }

        internal int ProducerInvocationCount =>
            File.Exists(invocationCount)
                ? int.Parse(File.ReadAllText(invocationCount).Trim(), System.Globalization.CultureInfo.InvariantCulture)
                : 0;

        internal ProcessOutput Run()
        {
            var script = Path.Combine(FindRepositoryRoot(), "Meta", "StrataLint", "scripts", "lean-report-pair.sh");
            return BoundedProcessRunner.Run(
                "env",
                [
                    $"STRATALINT_REPORT_METRICS_LOG={metricsLog}",
                    $"STRATALINT_SUPERVISOR_ROOT={Path.Combine(temporary.Path, "supervisor")}",
                    "bash",
                    script,
                    "--single",
                    "--producer", producer,
                    "--lake-bin", "/usr/bin/true",
                    "--candidate-root", candidateRoot,
                    "--candidate-output", candidateReport,
                ],
                temporary.Path,
                TimeSpan.FromSeconds(30),
                1024 * 1024);
        }

        internal void AppendProducerComment() =>
            File.AppendAllText(producer, "\n# producer mutation\n", new UTF8Encoding(false));

        internal JsonDocument ReadCandidateProvenance() =>
            JsonDocument.Parse(File.ReadAllBytes(candidateReport + ".provenance.json"));

        internal IReadOnlyList<JsonElement> ReadMetrics() => File.ReadAllLines(metricsLog)
            .Select(line => JsonDocument.Parse(line).RootElement.Clone())
            .ToArray();

        internal ProcessOutput VerifyCandidateManifest()
        {
            var helper = Path.Combine(FindRepositoryRoot(), InputHelperPath);
            var manifest = Path.Combine(temporary.Path, "candidate-modules.tsv");
            var generated = BoundedProcessRunner.Run(
                "bash",
                [helper, "manifest", "--repository", candidateRoot, "--report", candidateReport],
                temporary.Path,
                TimeSpan.FromSeconds(30),
                1024 * 1024);
            Assert.Equal(0, generated.ExitCode);
            File.WriteAllBytes(manifest, generated.StandardOutput);
            return BoundedProcessRunner.Run(
                "bash",
                [helper, "verify-manifest", "--repository", candidateRoot, "--report", candidateReport, "--manifest", manifest],
                temporary.Path,
                TimeSpan.FromSeconds(30),
                1024 * 1024);
        }

        public void Dispose() => temporary.Dispose();

        private static void InitializeRepository(string root)
        {
            Directory.CreateDirectory(Path.Combine(root, "D5"));
            Directory.CreateDirectory(Path.Combine(root, "Meta", "StrataLint", "lean-inspector"));
            File.WriteAllText(
                Path.Combine(root, "Trureturing.lean"),
                "import D5.Probe\n",
                new UTF8Encoding(false));
            File.WriteAllText(
                Path.Combine(root, "D5", "Probe.lean"),
                "theorem probe : True := by trivial\n",
                new UTF8Encoding(false));
            File.WriteAllText(
                Path.Combine(root, "lean-toolchain"),
                "leanprover/lean4:v4.31.0\n",
                new UTF8Encoding(false));
            File.WriteAllText(
                Path.Combine(root, "lakefile.toml"),
                "name = \"Fixture\"\n",
                new UTF8Encoding(false));
            File.WriteAllText(
                Path.Combine(root, "lake-manifest.json"),
                "{\"version\":\"1.1.0\"}\n",
                new UTF8Encoding(false));
            File.WriteAllText(
                Path.Combine(root, "Meta", "StrataLint", "lean-inspector", "inspect.sh"),
                "#!/usr/bin/env bash\n",
                new UTF8Encoding(false));
            File.WriteAllText(
                Path.Combine(root, "Meta", "StrataLint", "lean-inspector", "Inspector.lean"),
                "def residentFixture : True := by trivial\n",
                new UTF8Encoding(false));
            WriteProducerInput(root, InputHelperPath);
            WriteProducerInput(root, MergeCommandPath);
            WriteProducerInput(root, RawReportPath);
            WriteProducerInput(root, CanonicalWriterPath);
            WriteProducerInput(root, ScribeProgramPath);
            WriteProducerInput(root, CliProjectPath);
            WriteProducerInput(root, EngineProjectPath);
            WriteProducerInput(root, "Directory.Build.props");
        }

        private static void WriteProducerInput(string root, string relative)
        {
            var path = Path.Combine(root, relative.Replace('/', Path.DirectorySeparatorChar));
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            var contents = relative.EndsWith(".csproj", StringComparison.Ordinal)
                ? "<Project Sdk=\"Microsoft.NET.Sdk\" />\n"
                : relative.EndsWith(".props", StringComparison.Ordinal)
                    ? "<Project />\n"
                    : "fixture\n";
            File.WriteAllText(path, contents, new UTF8Encoding(false));
        }

        private static string FindRepositoryRoot()
        {
            for (var current = new DirectoryInfo(AppContext.BaseDirectory);
                 current is not null;
                 current = current.Parent)
            {
                if (File.Exists(Path.Combine(current.FullName, "CLAUDE.md"))) return current.FullName;
            }

            throw new DirectoryNotFoundException("Could not locate repository root.");
        }

        private const string FakeProducer = """
            #!/usr/bin/env bash
            set -euo pipefail
            repository=""
            output=""
            while [[ $# -gt 0 ]]; do
              case "$1" in
                --repository) repository="$2"; shift 2 ;;
                --output) output="$2"; shift 2 ;;
                *) exit 2 ;;
              esac
            done
            count_file="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)/invocations.txt"
            count=0
            if [[ -f "$count_file" ]]; then read -r count < "$count_file"; fi
            printf '%s\n' "$((count + 1))" > "$count_file"
            mkdir -p "$(dirname "$output")"
            source_hash="$(openssl dgst -sha256 "$repository/Trureturing.lean" | awk '{print $NF}')"
            printf '{"source_sha256":"%s"}\n' "$source_hash" > "$output"
            report_hash="$(openssl dgst -sha256 "$output" | awk '{print $NF}')"
            printf '%s  %s\n' "$report_hash" "$(basename "$output")" > "${output}.sha256"
            mkdir -p "${output}.logs"
            printf '%s\n' "$source_hash" > "${output}.logs/producer.log"
            """;
    }
}
