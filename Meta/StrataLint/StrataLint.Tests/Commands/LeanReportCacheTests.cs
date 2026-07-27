using System.Text;
using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.Tests;

// Contract for the content-addressed canonical-Lean-report cache ported from CI
// (.github/workflows/ci.yml, key stratalint-canonical-lean-report-v1-<address>)
// into the local devloop path. The cache is opt-in via STRATALINT_REPORT_CACHE_ROOT
// (never set in CI) and MUST be fail-closed: a hit is only served after the stored
// bundle re-verifies against the current tree; any anomaly evicts and reproduces.
//
// These tests never touch Mathlib, the real Lean slot, or the real report
// supervisor (the #452 tar pit). They drive the real lean-report-pair.sh and the
// real lean-report-input.sh against a stub producer + stub supervisor so the cache
// logic is exercised in isolation and in well under a second.
public sealed class LeanReportCacheTests
{
    [Fact]
    public void SecondProductionOfTheSameAddressIsServedFromCacheWithoutSlotOrProducer()
    {
        if (OperatingSystem.IsWindows()) return;
        using var world = new CacheWorld();

        var first = world.RunPair();
        Assert.Equal(0, first.ExitCode);
        Assert.Equal(1, world.ProducerRunCount);
        Assert.Equal(1, world.SlotAcquireCount);
        Assert.True(File.Exists(world.Output));
        var firstBytes = File.ReadAllBytes(world.Output);
        var address = world.AddressFrom(first);
        Assert.Matches("^[0-9a-f]{64}$", address);
        Assert.True(Directory.Exists(Path.Combine(world.CacheRoot, address)));

        var second = world.RunPair();
        Assert.Equal(0, second.ExitCode);
        // Cache hit: the stub producer is NOT re-invoked and NO Lean slot is taken.
        Assert.Equal(1, world.ProducerRunCount);
        Assert.Equal(1, world.SlotAcquireCount);
        Assert.Equal(address, world.AddressFrom(second));
        Assert.Equal(firstBytes, File.ReadAllBytes(world.Output));
        Assert.True(File.Exists(world.Output + ".sha256"));
        Assert.True(File.Exists(world.Output + ".input.attestation"));
        Assert.Contains(
            "\"mode\":\"cached\"",
            File.ReadAllText(world.Output + ".provenance.json"),
            StringComparison.Ordinal);
    }

    [Fact]
    public void CorruptedCacheReportFailsClosedAndIsReproduced()
    {
        if (OperatingSystem.IsWindows()) return;
        using var world = new CacheWorld();

        var first = world.RunPair();
        Assert.Equal(0, first.ExitCode);
        Assert.Equal(1, world.ProducerRunCount);
        var address = world.AddressFrom(first);
        var cachedReport = Path.Combine(world.CacheRoot, address, "raw-lean-report.json");
        Assert.True(File.Exists(cachedReport));

        // Tamper with the cached report so its bytes no longer match the sidecar.
        File.AppendAllText(cachedReport, "tampered\n");

        var second = world.RunPair();
        Assert.Equal(0, second.ExitCode);
        // Fail-closed: the corrupted entry is evicted and the report is reproduced.
        Assert.Equal(2, world.ProducerRunCount);
        Assert.True(File.Exists(world.Output));
        Assert.Contains(
            "\"mode\":\"produced\"",
            File.ReadAllText(world.Output + ".provenance.json"),
            StringComparison.Ordinal);
        // The re-produced report re-populates a clean, self-consistent cache entry.
        Assert.Equal(
            File.ReadAllBytes(world.Output),
            File.ReadAllBytes(Path.Combine(world.CacheRoot, address, "raw-lean-report.json")));
    }

    [Fact]
    public void ChangingAKeyedInputYieldsANewAddressAndMisses()
    {
        if (OperatingSystem.IsWindows()) return;
        using var world = new CacheWorld();

        var first = world.RunPair();
        Assert.Equal(0, first.ExitCode);
        Assert.Equal(1, world.ProducerRunCount);
        var address = world.AddressFrom(first);

        // Mutate a source file that participates in the content address.
        File.WriteAllText(
            Path.Combine(world.Repo, "D5", "Sample.lean"),
            "-- d5 stub (mutated)\n");

        var second = world.RunPair();
        Assert.Equal(0, second.ExitCode);
        var mutatedAddress = world.AddressFrom(second);
        Assert.NotEqual(address, mutatedAddress);
        // A new address cannot hit the prior entry, so the producer runs again.
        Assert.Equal(2, world.ProducerRunCount);
    }

    [Fact]
    public void CacheIsOptInAndDisabledWhenTheEnvironmentIsUnset()
    {
        if (OperatingSystem.IsWindows()) return;
        using var world = new CacheWorld();

        Assert.Equal(0, world.RunPair(cacheEnabled: false).ExitCode);
        Assert.Equal(0, world.RunPair(cacheEnabled: false).ExitCode);
        // With no cache root (the CI configuration) every call produces from scratch.
        Assert.Equal(2, world.ProducerRunCount);
        Assert.Equal(2, world.SlotAcquireCount);
        Assert.False(Directory.Exists(world.CacheRoot));
    }

    private sealed class CacheWorld : IDisposable
    {
        private readonly TemporaryDirectory _tmp = new();

        internal CacheWorld()
        {
            var repositoryRoot = FindRepositoryRoot();
            Repo = Path.Combine(_tmp.Path, "repo");
            CacheRoot = Path.Combine(_tmp.Path, "cache");
            SlotLog = Path.Combine(_tmp.Path, "slot.log");
            ProducerLog = Path.Combine(_tmp.Path, "producer.log");
            Output = Path.Combine(_tmp.Path, "out", "raw-lean-report.json");

            var inspectorDir = Path.Combine(Repo, "Meta", "StrataLint", "lean-inspector");
            var scriptsDir = Path.Combine(Repo, "Meta", "StrataLint", "scripts");
            var reportDir = Path.Combine(scriptsDir, "report");
            Directory.CreateDirectory(inspectorDir);
            Directory.CreateDirectory(reportDir);
            Directory.CreateDirectory(Path.Combine(Repo, "D5"));

            // Minimal repository inputs that lean-report-input.sh hashes into the address.
            File.WriteAllText(Path.Combine(Repo, "Trureturing.lean"), "-- stub\n");
            File.WriteAllText(Path.Combine(Repo, "lean-toolchain"), "leanprover/lean4:stub\n");
            File.WriteAllText(Path.Combine(Repo, "lake-manifest.json"), "{}\n");
            File.WriteAllText(Path.Combine(Repo, "lakefile.toml"), "name = \"stub\"\n");
            File.WriteAllText(Path.Combine(Repo, "D5", "Sample.lean"), "-- d5 stub\n");
            File.WriteAllText(Path.Combine(inspectorDir, "Inspector.lean"), "-- inspector stub\n");

            Producer = Path.Combine(inspectorDir, "inspect.sh");
            WriteExecutable(Producer, StubProducer);
            WriteExecutable(
                Path.Combine(reportDir, "report-supervisor.sh"),
                StubSupervisor);

            // The real scripts under test, copied verbatim from the repository.
            PairScript = Path.Combine(scriptsDir, "lean-report-pair.sh");
            File.Copy(
                Path.Combine(repositoryRoot, "Meta", "StrataLint", "scripts", "lean-report-pair.sh"),
                PairScript);
            File.Copy(
                Path.Combine(repositoryRoot, "Meta", "StrataLint", "scripts", "report", "lean-report-input.sh"),
                Path.Combine(reportDir, "lean-report-input.sh"));
            MakeExecutable(PairScript);
            MakeExecutable(Path.Combine(reportDir, "lean-report-input.sh"));
        }

        internal string Repo { get; }

        internal string CacheRoot { get; }

        internal string SlotLog { get; }

        internal string ProducerLog { get; }

        internal string Output { get; }

        internal string Producer { get; }

        internal string PairScript { get; }

        internal int ProducerRunCount => CountLines(ProducerLog);

        internal int SlotAcquireCount => CountLines(SlotLog);

        internal ProcessOutput RunPair(bool cacheEnabled = true)
        {
            var arguments = new List<string>
            {
                $"STUB_SLOT_LOG={SlotLog}",
                $"STUB_PRODUCER_LOG={ProducerLog}",
                "STUB_REPORT_CONTENT={\"schema\":\"stub-lean-report\",\"v\":1}",
            };
            if (cacheEnabled) arguments.Add($"STRATALINT_REPORT_CACHE_ROOT={CacheRoot}");
            arguments.AddRange(
            [
                PairScript,
                "--single",
                "--producer", Producer,
                "--lake-bin", "/bin/echo",
                "--candidate-root", Repo,
                "--candidate-output", Output,
            ]);

            return BoundedProcessRunner.Run(
                "env",
                arguments,
                Repo,
                TimeSpan.FromSeconds(60),
                1024 * 1024);
        }

        internal string AddressFrom(ProcessOutput output)
        {
            var text = Encoding.UTF8.GetString(output.StandardOutput);
            var match = Regex.Match(
                text,
                "content_address=sha256:([0-9a-f]{64})",
                RegexOptions.CultureInvariant);
            Assert.True(match.Success, $"no content address in pair output:\n{text}");
            return match.Groups[1].Value;
        }

        public void Dispose() => _tmp.Dispose();

        private static int CountLines(string path) =>
            File.Exists(path)
                ? File.ReadAllLines(path).Count(static line => line.Length > 0)
                : 0;

        private static void WriteExecutable(string path, string content)
        {
            File.WriteAllText(path, content);
            MakeExecutable(path);
        }

        private static void MakeExecutable(string path)
        {
            if (OperatingSystem.IsWindows()) return;
            File.SetUnixFileMode(
                path,
                UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute
                    | UnixFileMode.GroupRead | UnixFileMode.GroupExecute
                    | UnixFileMode.OtherRead | UnixFileMode.OtherExecute);
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

        // Records each invocation, writes a byte-stable canned report + sidecar, and
        // exits 0 in well under a second. Mirrors the inspect.sh contract consumed by
        // lean-report-pair.sh: --repository <root> --output <file>.
        private const string StubProducer = """
            #!/usr/bin/env bash
            set -euo pipefail
            printf 'run\n' >> "$STUB_PRODUCER_LOG"
            output=""
            while [[ $# -gt 0 ]]; do
              case "$1" in
                --repository) shift 2 ;;
                --output) output="$2"; shift 2 ;;
                *) shift ;;
              esac
            done
            [[ -n "$output" ]] || { echo "stub-producer: no --output" >&2; exit 2; }
            mkdir -p "$(dirname "$output")"
            printf '%s\n' "$STUB_REPORT_CONTENT" > "$output"
            if command -v sha256sum >/dev/null 2>&1; then
              h="$(sha256sum "$output" | awk '{print $1}')"
            elif command -v openssl >/dev/null 2>&1; then
              h="$(openssl dgst -sha256 "$output" | awk '{print $NF}')"
            else
              h="$(shasum -a 256 "$output" | awk '{print $1}')"
            fi
            printf '%s  %s\n' "$h" "$(basename "$output")" > "${output}.sha256"
            """;

        // Records each slot acquisition, then execs the wrapped worker. A cache hit
        // returns before the supervisor is ever invoked, so the slot log stays flat.
        private const string StubSupervisor = """
            #!/usr/bin/env bash
            set -euo pipefail
            printf 'slot\n' >> "$STUB_SLOT_LOG"
            while [[ $# -gt 0 && "$1" != "--" ]]; do shift; done
            [[ "${1:-}" == "--" ]] && shift
            exec "$@"
            """;
    }
}
