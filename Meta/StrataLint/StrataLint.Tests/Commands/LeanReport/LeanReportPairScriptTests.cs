using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LeanReportPairScriptTests
{
    private const string InputHelperPath = "Meta/StrataLint/scripts/report/lean-report-input.sh";
    private const string MergeCommandPath = "Meta/StrataLint/StrataLint.Cli/Commands/LeanReportMergeCommand.cs";
    private const string RawReportPath = "Meta/StrataLint/StrataLint.Engine/Snapshot/RawLeanReportArtifact.cs";
    private const string CanonicalWriterPath = "Meta/StrataLint/StrataLint.Engine/Snapshot/StructuredCanonicalWriter.cs";
    [Fact]
    public void EqualInputsRunProducerOnceAndAttestBaselineReuse()
    {
        using var fixture = new LeanReportPairFixture();

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(1, fixture.ProducerInvocationCount);
        Assert.Equal(fixture.CandidateReportBytes, fixture.BaselineReportBytes);
        using var candidate = fixture.ReadCandidateProvenance();
        using var baseline = fixture.ReadBaselineProvenance();
        Assert.Equal("produced", candidate.RootElement.GetProperty("mode").GetString());
        Assert.Equal("candidate", candidate.RootElement.GetProperty("source_side").GetString());
        Assert.Equal("reused", baseline.RootElement.GetProperty("mode").GetString());
        Assert.Equal("candidate", baseline.RootElement.GetProperty("source_side").GetString());
        Assert.Equal(
            candidate.RootElement.GetProperty("input_address").GetString(),
            baseline.RootElement.GetProperty("input_address").GetString());
        Assert.Equal(
            candidate.RootElement.GetProperty("report_sha256").GetString(),
            baseline.RootElement.GetProperty("report_sha256").GetString());
        Assert.Contains(
            "LEAN_REPORT_PROVENANCE side=baseline mode=reused",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("source")]
    [InlineData("toolchain")]
    [InlineData("lakefile")]
    [InlineData("manifest")]
    public void AnyRepositoryInputMismatchRunsBothProducers(string mutation)
    {
        using var fixture = new LeanReportPairFixture();
        fixture.MutateBaseline(mutation);

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.True(
            fixture.ProducerInvocationCount == 2,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
        using var candidate = fixture.ReadCandidateProvenance();
        using var baseline = fixture.ReadBaselineProvenance();
        Assert.Equal("produced", baseline.RootElement.GetProperty("mode").GetString());
        Assert.Equal("baseline", baseline.RootElement.GetProperty("source_side").GetString());
        Assert.NotEqual(
            candidate.RootElement.GetProperty("input_address").GetString(),
            baseline.RootElement.GetProperty("input_address").GetString());
    }

    [Fact]
    public void BaselineMissingProducerInputDisablesReuseWithoutFailingProduction()
    {
        using var fixture = new LeanReportPairFixture();
        fixture.RemoveBaselineProducerInput(MergeCommandPath);

        var result = fixture.Run();

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.True(
            fixture.ProducerInvocationCount == 2,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
        using var candidate = fixture.ReadCandidateProvenance();
        using var baseline = fixture.ReadBaselineProvenance();
        Assert.NotEqual(
            candidate.RootElement.GetProperty("input_address").GetString(),
            baseline.RootElement.GetProperty("input_address").GetString());
    }

    [Fact]
    public void CandidateMissingProducerInputRemainsAHardFailure()
    {
        using var fixture = new LeanReportPairFixture();
        fixture.RemoveCandidateProducerInput(MergeCommandPath);

        var result = fixture.Run();

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("repository input is absent", Encoding.UTF8.GetString(result.StandardError));
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
    public void PairProductionWritesMeasurementsToCallerHeldLog()
    {
        using var fixture = new LeanReportPairFixture();

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        var metrics = fixture.ReadMetrics();
        var metric = Assert.Single(metrics);
        Assert.Equal("resource", metric.GetProperty("kind").GetString());
        Assert.Equal("lean-producer-candidate", metric.GetProperty("role").GetString());
    }

    [Fact]
    public void InvalidModuleManifestFallsThroughToFullProduction()
    {
        var script = File.ReadAllText(Path.Combine(
            FindRepositoryRoot(), "Meta", "StrataLint", "scripts", "lean-report-pair.sh"));

        Assert.Contains("&& \"$INPUT_HELPER\" verify-manifest", script, StringComparison.Ordinal);
        Assert.Contains("else\n    \"$SUPERVISOR\" --role \"lean-producer-$side\"", script, StringComparison.Ordinal);
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
        private readonly string baselineRoot;
        private readonly string artifacts;
        private readonly string producerDirectory;
        private readonly string producer;
        private readonly string invocationCount;
        private readonly string candidateReport;
        private readonly string baselineReport;
        private readonly string metricsLog;

        internal LeanReportPairFixture()
        {
            candidateRoot = Path.Combine(temporary.Path, "candidate");
            baselineRoot = Path.Combine(temporary.Path, "baseline");
            artifacts = Path.Combine(temporary.Path, "reports");
            producerDirectory = Path.Combine(temporary.Path, "producer");
            producer = Path.Combine(producerDirectory, "inspect.sh");
            invocationCount = Path.Combine(producerDirectory, "invocations.txt");
            candidateReport = Path.Combine(artifacts, "candidate.json");
            baselineReport = Path.Combine(artifacts, "baseline.json");
            metricsLog = Path.Combine(temporary.Path, "measurements.jsonl");
            InitializeRepository(candidateRoot);
            InitializeRepository(baselineRoot);
            Directory.CreateDirectory(artifacts);
            Directory.CreateDirectory(producerDirectory);
            File.WriteAllText(
                Path.Combine(producerDirectory, "Inspector.lean"),
                "def producerFixture : True := by trivial\n",
                new UTF8Encoding(false));
            File.WriteAllText(producer, FakeProducer, new UTF8Encoding(false));
            foreach (var root in new[] { candidateRoot, baselineRoot })
            {
                File.WriteAllText(Path.Combine(root, "Meta", "StrataLint", "lean-inspector", "inspect.sh"), FakeProducer, new UTF8Encoding(false));
                File.WriteAllText(
                    Path.Combine(root, "Meta", "StrataLint", "lean-inspector", "Inspector.lean"),
                    "def producerFixture : True := by trivial\n",
                    new UTF8Encoding(false));
            }
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

        internal byte[] CandidateReportBytes => File.ReadAllBytes(candidateReport);

        internal byte[] BaselineReportBytes => File.ReadAllBytes(baselineReport);

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
                    "--producer", producer,
                    "--lake-bin", "/usr/bin/true",
                    "--candidate-root", candidateRoot,
                    "--candidate-output", candidateReport,
                    "--baseline-root", baselineRoot,
                    "--baseline-output", baselineReport,
                ],
                temporary.Path,
                TimeSpan.FromSeconds(30),
                1024 * 1024);
        }

        internal void MutateBaseline(string mutation)
        {
            var relativePath = mutation switch
            {
                "source" => "D5/Probe.lean",
                "toolchain" => "lean-toolchain",
                "lakefile" => "lakefile.toml",
                "manifest" => "lake-manifest.json",
                "inspector" => Path.Combine("Meta", "StrataLint", "lean-inspector", "Inspector.lean"),
                _ => throw new InvalidOperationException($"unknown mutation {mutation}"),
            };
            File.AppendAllText(
                Path.Combine(baselineRoot, relativePath),
                "mutation\n",
                new UTF8Encoding(false));
        }

        internal void AppendProducerComment() =>
            File.AppendAllText(producer, "\n# producer mutation\n", new UTF8Encoding(false));

        internal void RemoveBaselineProducerInput(string relative) =>
            File.Delete(Path.Combine(baselineRoot, relative.Replace('/', Path.DirectorySeparatorChar)));

        internal void RemoveCandidateProducerInput(string relative) =>
            File.Delete(Path.Combine(candidateRoot, relative.Replace('/', Path.DirectorySeparatorChar)));

        internal JsonDocument ReadCandidateProvenance() =>
            JsonDocument.Parse(File.ReadAllBytes(candidateReport + ".provenance.json"));

        internal JsonDocument ReadBaselineProvenance() =>
            JsonDocument.Parse(File.ReadAllBytes(baselineReport + ".provenance.json"));

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
        }

        private static void WriteProducerInput(string root, string relative)
        {
            var path = Path.Combine(root, relative.Replace('/', Path.DirectorySeparatorChar));
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, "fixture\n", new UTF8Encoding(false));
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
