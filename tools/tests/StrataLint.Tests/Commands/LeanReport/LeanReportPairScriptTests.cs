using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Lean report environment")]
public sealed class LeanReportPairScriptTests
{
    private const string InputHelperPath = "tools/scripts/report/lean-report-input.sh";
    private const string RawReportPath = "tools/StrataLint.Engine/Snapshot/RawLeanReportArtifact.cs";
    private const string CanonicalWriterPath = "tools/Trureturing.Truth/StructuredCanonicalWriter.cs";
    private const string ScribeProgramPath = "tools/StrataLint.Scribe/ScribeProgram.cs";
    private static readonly string CliProjectPath = string.Join(
        '/', "tools", "StrataLint.Cli", "StrataLint.Cli.csproj");
    private static readonly string EngineProjectPath = string.Join(
        '/', "tools", "StrataLint.Engine", "StrataLint.Engine.csproj");
    [Fact]
    public void SingleProductionWritesOneVerifiedCandidateBundle()
    {
        using var fixture = new LeanReportPairFixture();
        fixture.SeedLegacyCandidateMaterials();

        var result = fixture.Run();

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.Equal(1, fixture.ProducerInvocationCount);
        Assert.False(fixture.CandidateLegacyMaterialsExist);
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
    public void CacheEnsureRunsBeforeTheCandidateLakeTreeExists()
    {
        using var fixture = new LeanReportPairFixture();

        var result = fixture.Run();

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.Equal(["absent"], fixture.CacheEnsureLakeStates);
        Assert.Equal(1, fixture.ProducerInvocationCount);
    }

    [Fact]
    public void FailedCacheEnsurePreservesExitCodeBeforeProducerOrStaging()
    {
        using var fixture = new LeanReportPairFixture();

        var result = fixture.Run(cacheEnsureExitCode: 73);

        Assert.Equal(73, result.ExitCode);
        Assert.Equal(["absent"], fixture.CacheEnsureLakeStates);
        Assert.Equal(0, fixture.ProducerInvocationCount);
        Assert.False(fixture.CandidateLakeExists);
    }

    [Fact]
    public void FailedCacheEnsureReceiptReachesCallerOnStandardError()
    {
        using var fixture = new LeanReportPairFixture();

        var result = fixture.Run(cacheEnsureExitCode: 73);

        Assert.Equal(73, result.ExitCode);
        Assert.Contains(
            "LEAN_CACHE {\"status\":\"failed\",\"method\":\"fake\"}",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
        Assert.DoesNotContain(
            "LEAN_CACHE ",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
        Assert.False(fixture.CandidateLogExists);
    }

    [Fact]
    public void TermAfterCacheEnsureReceiptPreservesSignalExitCode()
    {
        using var fixture = new LeanReportPairFixture();

        var result = fixture.Run(signalPairAfterReceipt: true);

        Assert.Equal(143, result.ExitCode);
        Assert.Contains(
            "LEAN_CACHE {\"status\":\"seeded\",\"method\":\"fake\"}",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
        Assert.Equal(0, fixture.ProducerInvocationCount);
        Assert.False(fixture.CandidateLogExists);
    }

    [Fact]
    public void CacheEnsureReceiptReachesCallerInsteadOfStagingSidecar()
    {
        using var fixture = new LeanReportPairFixture();

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Contains(
            "LEAN_CACHE {\"status\":\"seeded\",\"method\":\"fake\"}",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
        Assert.DoesNotContain(
            "LEAN_CACHE ",
            fixture.ReadCandidateLogText(),
            StringComparison.Ordinal);
    }

    [Fact]
    public void MissingCacheEnsureReportsItsExactCandidatePath()
    {
        using var fixture = new LeanReportPairFixture();
        fixture.DeleteCacheEnsure();

        var result = fixture.Run();

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(
            $"lean-report-pair: cache ensure is absent or not a readable regular file: {fixture.CanonicalCacheEnsurePath}\n",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
        Assert.Equal(0, fixture.ProducerInvocationCount);
        Assert.False(fixture.CandidateLakeExists);
    }

    [Fact]
    public void PairScriptPinsPerModuleReuseOff()
    {
        var script = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(), "tools", "scripts", "lean-report-pair.sh"));

        Assert.Contains("Per-module reuse is disabled", script, StringComparison.Ordinal);
        Assert.DoesNotContain("--module-cache-report", script, StringComparison.Ordinal);
        Assert.DoesNotContain("--module-cache-manifest", script, StringComparison.Ordinal);
        Assert.DoesNotContain("--modules-file", script, StringComparison.Ordinal);
    }

    private sealed class LeanReportPairFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        private readonly string candidateRoot;
        private readonly string producerDirectory;
        private readonly string producer;
        private readonly string invocationCount;
        private readonly string candidateReport;
        private readonly string cacheEnsureLog;
        private readonly string canonicalCandidateRoot;

        internal LeanReportPairFixture()
        {
            candidateRoot = Path.Combine(temporary.Path, "candidate");
            producerDirectory = Path.Combine(temporary.Path, "producer");
            producer = Path.Combine(producerDirectory, "inspect.sh");
            invocationCount = Path.Combine(producerDirectory, "invocations.txt");
            candidateReport = Path.Combine(
                candidateRoot, ".lake", "build", "stratalint", "candidate.json");
            cacheEnsureLog = Path.Combine(temporary.Path, "cache-ensure.log");
            InitializeRepository(candidateRoot);
            var physicalRoot = TestProcessRunner.Run(
                "pwd",
                ["-P"],
                candidateRoot,
                BoundedProcessRunner.HangDetectionBudget,
                4096);
            Assert.Equal(0, physicalRoot.ExitCode);
            canonicalCandidateRoot = Encoding.UTF8.GetString(physicalRoot.StandardOutput).Trim();
            Directory.CreateDirectory(producerDirectory);
            File.WriteAllText(
                Path.Combine(producerDirectory, "Inspector.lean"),
                "def producerFixture : True := by trivial\n",
                new UTF8Encoding(false));
            File.WriteAllText(producer, FakeProducer, new UTF8Encoding(false));
            File.WriteAllText(Path.Combine(candidateRoot, "tools", "lean-inspector", "inspect.sh"), FakeProducer, new UTF8Encoding(false));
            File.WriteAllText(
                Path.Combine(candidateRoot, "tools", "lean-inspector", "Inspector.lean"),
                "def producerFixture : True := by trivial\n",
                new UTF8Encoding(false));
            File.WriteAllText(CacheEnsurePath, FakeCacheEnsure, new UTF8Encoding(false));
            var chmod = TestProcessRunner.Run(
                "chmod",
                ["+x", producer],
                temporary.Path,
                BoundedProcessRunner.HangDetectionBudget,
                4096);
            Assert.Equal(0, chmod.ExitCode);
        }

        internal int ProducerInvocationCount =>
            File.Exists(invocationCount)
                ? int.Parse(File.ReadAllText(invocationCount).Trim(), System.Globalization.CultureInfo.InvariantCulture)
                : 0;

        internal string CacheEnsurePath => Path.Combine(
            candidateRoot, "tools", "scripts", "worktree", "lean-cache-ensure.sh");

        internal string CanonicalCacheEnsurePath => Path.Combine(
            canonicalCandidateRoot, "tools", "scripts", "worktree", "lean-cache-ensure.sh");

        internal IReadOnlyList<string> CacheEnsureLakeStates =>
            File.Exists(cacheEnsureLog) ? File.ReadAllLines(cacheEnsureLog) : [];

        internal bool CandidateLakeExists =>
            Directory.Exists(Path.Combine(candidateRoot, ".lake"));

        internal bool CandidateLogExists =>
            Directory.Exists(candidateReport + ".logs");

        internal bool CandidateLegacyMaterialsExist =>
            Directory.Exists(candidateReport + ".materials");

        internal ProcessOutput Run(
            int cacheEnsureExitCode = 0,
            bool signalPairAfterReceipt = false)
        {
            var script = Path.Combine(TestRepositoryLayout.FindRoot(), "tools", "scripts", "lean-report-pair.sh");
            return TestProcessRunner.Run(
                "env",
                [
                    $"STRATALINT_SUPERVISOR_ROOT={Path.Combine(temporary.Path, "supervisor")}",
                    $"STUB_LEAN_CACHE_ENSURE_LOG={cacheEnsureLog}",
                    $"STUB_LEAN_CACHE_ENSURE_EXIT_CODE={cacheEnsureExitCode}",
                    $"STUB_LEAN_CACHE_ENSURE_SIGNAL_PARENT={(signalPairAfterReceipt ? 1 : 0)}",
                    "bash",
                    script,
                    "--producer", producer,
                    "--lake-bin", "/usr/bin/true",
                    "--candidate-root", candidateRoot,
                    "--candidate-output", candidateReport,
                ],
                temporary.Path,
                BoundedProcessRunner.HangDetectionBudget,
                1024 * 1024);
        }

        internal void DeleteCacheEnsure() => File.Delete(CacheEnsurePath);

        internal void AppendProducerComment() =>
            File.AppendAllText(producer, "\n# producer mutation\n", new UTF8Encoding(false));

        internal void SeedLegacyCandidateMaterials() =>
            Directory.CreateDirectory(Path.Combine(candidateReport + ".materials", "sha256"));

        internal JsonDocument ReadCandidateProvenance() =>
            JsonDocument.Parse(File.ReadAllBytes(candidateReport + ".provenance.json"));

        internal string ReadCandidateLogText() => string.Join(
            '\n',
            Directory.EnumerateFiles(candidateReport + ".logs", "*", SearchOption.AllDirectories)
                .Order(StringComparer.Ordinal)
                .Select(File.ReadAllText));

        public void Dispose() => temporary.Dispose();

        private static void InitializeRepository(string root)
        {
            Directory.CreateDirectory(Path.Combine(root, "D5"));
            Directory.CreateDirectory(Path.Combine(root, "tools", "lean-inspector"));
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
                Path.Combine(root, "tools", "lean-inspector", "inspect.sh"),
                "#!/usr/bin/env bash\n",
                new UTF8Encoding(false));
            File.WriteAllText(
                Path.Combine(root, "tools", "lean-inspector", "Inspector.lean"),
                "def residentFixture : True := by trivial\n",
                new UTF8Encoding(false));
            WriteProducerInput(root, InputHelperPath);
            WriteProducerInput(root, RawReportPath);
            WriteProducerInput(root, CanonicalWriterPath);
            WriteProducerInput(root, ScribeProgramPath);
            WriteProducerInput(root, CliProjectPath);
            WriteProducerInput(root, EngineProjectPath);
            WriteProducerInput(root, "Directory.Build.props");
            Directory.CreateDirectory(Path.Combine(root, "tools", "scripts", "worktree"));
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


        private const string FakeCacheEnsure = """
            #!/usr/bin/env bash
            set -euo pipefail
            root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
            state=absent
            [[ ! -e "$root/.lake" ]] || state=present
            printf '%s\n' "$state" >> "$STUB_LEAN_CACHE_ENSURE_LOG"
            if [[ "$STUB_LEAN_CACHE_ENSURE_EXIT_CODE" -eq 0 ]]; then
              printf '%s\n' 'LEAN_CACHE {"status":"seeded","method":"fake"}'
            else
              printf '%s\n' 'LEAN_CACHE {"status":"failed","method":"fake"}' >&2
            fi
            if [[ "$STUB_LEAN_CACHE_ENSURE_SIGNAL_PARENT" -eq 1 ]]; then
              kill -TERM "$PPID"
            fi
            exit "$STUB_LEAN_CACHE_ENSURE_EXIT_CODE"
            """;

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
            printf '%s\n' 'stub material archive' > "${output}.materials.zip"
            source_hash="$(openssl dgst -sha256 "$repository/Trureturing.lean" | awk '{print $NF}')"
            printf '{"source_sha256":"%s"}\n' "$source_hash" > "$output"
            report_hash="$(openssl dgst -sha256 "$output" | awk '{print $NF}')"
            printf '%s  %s\n' "$report_hash" "$(basename "$output")" > "${output}.sha256"
            mkdir -p "${output}.logs"
            printf '%s\n' "$source_hash" > "${output}.logs/producer.log"
            """;
    }
}
