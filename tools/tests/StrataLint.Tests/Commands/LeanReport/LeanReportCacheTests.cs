using System.Security.Cryptography;
using System.Text;
using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.Tests;

// Contract for the opt-in content-addressed report cache. Hits re-verify against
// the current tree; anomalies evict and reproduce. Stubs drive the real cache and
// input scripts without Mathlib, the Lean slot, or the report supervisor.
public sealed class LeanReportCacheTests
{
    private const string RawReportPath = "tools/StrataLint.Engine/Snapshot/RawLeanReportArtifact.cs";
    private const string CanonicalWriterPath = "tools/Trureturing.Truth/StructuredCanonicalWriter.cs";
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
        Assert.False(Directory.Exists(Path.Combine(
            world.CacheRoot, address, "raw-lean-report.json.logs")));

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
        Assert.False(Directory.Exists(world.Output + ".logs"));
    }

    [Fact]
    public void ExactCacheEntryWithLegacyLogsFailsClosedAndIsReproduced()
    {
        if (OperatingSystem.IsWindows()) return;
        using var world = new CacheWorld();
        var first = world.RunPair();
        Assert.Equal(0, first.ExitCode);
        var address = world.AddressFrom(first);
        world.AddLegacyLogsToCacheEntry(address);

        var second = world.RunPair();

        Assert.Equal(0, second.ExitCode);
        Assert.Equal(2, world.ProducerRunCount);
        Assert.Equal("produced", world.LiveMode());
        Assert.False(world.CacheEntryHasLogs(address));
    }

    [Fact]
    public void ExactCacheEntryWithDanglingLogsSymlinkFailsClosedAndIsReproduced()
    {
        if (OperatingSystem.IsWindows()) return;
        using var world = new CacheWorld();
        var first = world.RunPair();
        Assert.Equal(0, first.ExitCode);
        var address = world.AddressFrom(first);
        world.AddDanglingLogsSymlinkToCacheEntry(address);

        var second = world.RunPair();

        Assert.Equal(0, second.ExitCode);
        Assert.Equal(2, world.ProducerRunCount);
        Assert.Equal("produced", world.LiveMode());
        Assert.False(world.CacheEntryHasLogs(address));
    }

    [Fact]
    public void ProducedBundleWithLogsPassesVerificationAndPublishesLiveLogs()
    {
        if (OperatingSystem.IsWindows()) return;
        using var world = new CacheWorld();

        var result = world.RunPair(cacheEnabled: false);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("produced", world.LiveMode());
        Assert.True(world.LiveLogsExist());
    }

    [Fact]
    public void ProducedBundleWithoutLogsFailsClosedBeforePublication()
    {
        if (OperatingSystem.IsWindows()) return;
        using var world = new CacheWorld();

        var result = world.RunPair(cacheEnabled: false, omitProducerLogs: true);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Equal(1, world.ProducerRunCount);
        Assert.False(world.LiveBundleExists());
    }

    [Fact]
    public void ProducedBundleWithLogFileFailsClosedBeforePublication()
    {
        if (OperatingSystem.IsWindows()) return;
        using var world = new CacheWorld();

        var result = world.RunPair(cacheEnabled: false, producerLogsAsFile: true);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Equal(1, world.ProducerRunCount);
        Assert.False(world.LiveBundleExists());
    }

    [Fact]
    public void ProducedBundleWithEmptyLogsDirectoryFailsClosedBeforePublication()
    {
        if (OperatingSystem.IsWindows()) return;
        using var world = new CacheWorld();

        var result = world.RunPair(cacheEnabled: false, emptyProducerLogs: true);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Equal(1, world.ProducerRunCount);
        Assert.False(world.LiveBundleExists());
    }

    [Fact]
    public void CachedBundleWithLogsInjectedAfterRestoreFailsClosedBeforePublication()
    {
        if (OperatingSystem.IsWindows()) return;
        using var world = new CacheWorld();
        var first = world.RunPair();
        Assert.Equal(0, first.ExitCode);
        var prior = world.SnapshotLiveBundle();

        var second = world.RunPair(injectCachedLogs: true);

        Assert.NotEqual(0, second.ExitCode);
        Assert.Equal(1, world.ProducerRunCount);
        Assert.Equal(prior, world.SnapshotLiveBundle());
        Assert.Contains(
            "cached bundle contains producer logs",
            Encoding.UTF8.GetString(second.StandardError),
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

    [Fact]
    public void TamperedAttestationFailsClosedAndIsReproduced()
    {
        if (OperatingSystem.IsWindows()) return;
        using var world = new CacheWorld();

        var first = world.RunPair();
        Assert.Equal(0, first.ExitCode);
        Assert.Equal(1, world.ProducerRunCount);
        var address = world.AddressFrom(first);
        var attestation = Path.Combine(
            world.CacheRoot, address, "raw-lean-report.json.input.attestation");
        Assert.True(File.Exists(attestation));

        // Point the attestation at a repository address that no longer matches the
        // live tree. The report bytes and .sha256 stay valid, so ONLY the
        // lean-report-input.sh verify (address re-derivation against the current
        // tree) can catch this — the core stale/forgery defence that the earlier
        // "change a tree file -> address changes -> miss" tests never exercise.
        var tampered = Regex.Replace(
            File.ReadAllText(attestation),
            "repository_input_sha256=[0-9a-f]{64}",
            "repository_input_sha256=" + new string('a', 64));
        File.WriteAllText(attestation, tampered);

        var second = world.RunPair();
        Assert.Equal(0, second.ExitCode);
        // verify rejects the tampered attestation -> evict -> reproduce.
        Assert.Equal(2, world.ProducerRunCount);
        Assert.Contains(
            "\"mode\":\"produced\"",
            File.ReadAllText(world.Output + ".provenance.json"),
            StringComparison.Ordinal);
    }

    [Fact]
    public void WorldWritableCacheRootIsNotTrusted()
    {
        if (OperatingSystem.IsWindows()) return;
        using var world = new CacheWorld();

        var first = world.RunPair();
        Assert.Equal(0, first.ExitCode);
        Assert.Equal(1, world.ProducerRunCount);
        var address = world.AddressFrom(first);
        Assert.True(Directory.Exists(Path.Combine(world.CacheRoot, address)));

        // A cache root any user could have planted or written into (predictable
        // shared-tmp path). Its re-verification anchors only PUBLIC tree inputs, so
        // a forged entry would self-consistently re-verify; the only defence is to
        // refuse to trust a group/other-writable (or foreign-owned) root.
        File.SetUnixFileMode(
            world.CacheRoot,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute
                | UnixFileMode.GroupRead | UnixFileMode.GroupWrite | UnixFileMode.GroupExecute
                | UnixFileMode.OtherRead | UnixFileMode.OtherWrite | UnixFileMode.OtherExecute);

        var second = world.RunPair();
        Assert.Equal(0, second.ExitCode);
        // Untrusted root: the existing entry is NOT served; the report is reproduced.
        Assert.Equal(2, world.ProducerRunCount);
    }

    [Fact]
    public void FailedProducerIsNeverStored()
    {
        if (OperatingSystem.IsWindows()) return;
        using var world = new CacheWorld();

        var result = world.RunPair(producerFails: true);
        Assert.NotEqual(0, result.ExitCode);
        Assert.Equal(1, world.ProducerRunCount);
        // The content address is printed before production begins, so it is
        // available even though the producer failed.
        var address = world.AddressFrom(result);
        Assert.False(Directory.Exists(Path.Combine(world.CacheRoot, address)));
        // A killed / rc!=0 producer must never leave a committed cache entry that a
        // later run could serve as a "good" report.
        Assert.Empty(world.CommittedCacheEntries());
    }

    [Theory]
    [InlineData("producer")]
    [InlineData("supervisor")]
    [InlineData("verification")]
    [InlineData("sidecar")]
    [InlineData("cache-restore")]
    public void FailedReplacementPreservesEveryPriorBundleByte(string stage)
    {
        if (OperatingSystem.IsWindows()) return;
        using var world = new CacheWorld();
        var cacheEnabled = stage == "cache-restore";
        var first = world.RunPair(cacheEnabled: cacheEnabled, reportVersion: 1);
        Assert.Equal(0, first.ExitCode);
        var prior = world.SnapshotLiveBundle();

        var failed = world.RunPair(
            cacheEnabled: cacheEnabled,
            failureStage: stage,
            reportVersion: 2);

        Assert.NotEqual(0, failed.ExitCode);
        Assert.Equal(prior, world.SnapshotLiveBundle());
    }

    [Fact]
    public void SuccessfulReplacementPublishesTheCompleteNewBundle()
    {
        if (OperatingSystem.IsWindows()) return;
        using var world = new CacheWorld();
        Assert.Equal(0, world.RunPair(cacheEnabled: false, reportVersion: 1).ExitCode);
        var prior = world.SnapshotLiveBundle();

        var replaced = world.RunPair(cacheEnabled: false, reportVersion: 2);

        Assert.Equal(0, replaced.ExitCode);
        Assert.NotEqual(prior, world.SnapshotLiveBundle());
        Assert.Equal(
            "{\"schema\":\"stub-lean-report\",\"v\":2}\n",
            File.ReadAllText(world.Output));
        Assert.Equal(
            "{\"schema\":\"stub-lean-report\",\"v\":2}\n",
            File.ReadAllText(Path.Combine(world.Output + ".logs", "producer.log")));
    }

    private sealed class CacheWorld : IDisposable
    {
        private readonly TemporaryDirectory _tmp = new();

        internal CacheWorld()
        {
            var repositoryRoot = TestRepositoryLayout.FindRoot();
            Repo = Path.Combine(_tmp.Path, "repo");
            CacheRoot = Path.Combine(_tmp.Path, "cache");
            SlotLog = Path.Combine(_tmp.Path, "slot.log");
            ProducerLog = Path.Combine(_tmp.Path, "producer.log");
            Output = Path.Combine(_tmp.Path, "out", "raw-lean-report.json");
            var bin = Path.Combine(_tmp.Path, "bin");

            var inspectorDir = Path.Combine(Repo, "tools", "lean-inspector");
            var scriptsDir = Path.Combine(Repo, "tools", "scripts");
            var reportDir = Path.Combine(scriptsDir, "report");
            var worktreeDir = Path.Combine(scriptsDir, "worktree");
            Directory.CreateDirectory(inspectorDir);
            Directory.CreateDirectory(reportDir);
            Directory.CreateDirectory(worktreeDir);
            Directory.CreateDirectory(Path.Combine(Repo, "D5"));
            Directory.CreateDirectory(bin);

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
            File.WriteAllText(
                Path.Combine(worktreeDir, "lean-cache-ensure.sh"),
                StubCacheEnsure);
            CopyWrapper = Path.Combine(bin, "cp");
            WriteExecutable(CopyWrapper, StubCopy);

            // The real scripts under test, copied verbatim from the repository.
            PairScript = Path.Combine(scriptsDir, "lean-report-pair.sh");
            File.Copy(
                Path.Combine(repositoryRoot, "tools", "scripts", "lean-report-pair.sh"),
                PairScript);
            File.Copy(
                Path.Combine(repositoryRoot, "tools", "scripts", "report", "lean-report-input.sh"),
                Path.Combine(reportDir, "lean-report-input.sh"));
            foreach (var relative in new[]
            {
                RawReportPath,
                CanonicalWriterPath,
            })
            {
                var path = Path.Combine(Repo, relative.Replace('/', Path.DirectorySeparatorChar));
                Directory.CreateDirectory(Path.GetDirectoryName(path)!);
                File.WriteAllText(path, "fixture\n");
            }
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

        internal string CopyWrapper { get; }

        internal int ProducerRunCount => CountLines(ProducerLog);

        internal int SlotAcquireCount => CountLines(SlotLog);

        internal IReadOnlyList<string> CommittedCacheEntries() =>
            Directory.Exists(CacheRoot)
                ? Directory.GetDirectories(CacheRoot)
                    .Where(static d => !Path.GetFileName(d).StartsWith(".tmp", StringComparison.Ordinal))
                    .ToArray()
                : [];

        internal ProcessOutput RunPair(
            bool cacheEnabled = true,
            bool producerFails = false,
            bool omitProducerLogs = false,
            bool producerLogsAsFile = false,
            bool emptyProducerLogs = false,
            bool injectCachedLogs = false,
            string? failureStage = null,
            int reportVersion = 1)
        {
            var arguments = new List<string>();
            if (!cacheEnabled)
            {
                // Seal against an ambient STRATALINT_REPORT_CACHE_ROOT leaking in from
                // the test runner's own environment: `env -u` strips it for the child.
                arguments.Add("-u");
                arguments.Add("STRATALINT_REPORT_CACHE_ROOT");
            }
            arguments.Add($"STUB_SLOT_LOG={SlotLog}");
            arguments.Add($"STUB_PRODUCER_LOG={ProducerLog}");
            arguments.Add($"STUB_REPORT_CONTENT={{\"schema\":\"stub-lean-report\",\"v\":{reportVersion}}}");
            if (producerFails || failureStage == "producer") arguments.Add("STUB_PRODUCER_FAIL=1");
            if (omitProducerLogs) arguments.Add("STUB_OMIT_LOGS=1");
            if (producerLogsAsFile) arguments.Add("STUB_LOGS_AS_FILE=1");
            if (emptyProducerLogs) arguments.Add("STUB_EMPTY_LOGS=1");
            if (injectCachedLogs) arguments.Add("STUB_INJECT_CACHED_LOGS=1");
            if (failureStage == "supervisor") arguments.Add("STUB_SUPERVISOR_FAIL=1");
            if (failureStage == "verification") arguments.Add("STUB_BAD_SHA=1");
            if (failureStage == "sidecar") arguments.Add("STUB_SIDECAR_FAIL=1");
            if (failureStage == "cache-restore") arguments.Add("STUB_CACHE_COPY_FAIL=1");
            if (cacheEnabled) arguments.Add($"STRATALINT_REPORT_CACHE_ROOT={CacheRoot}");
            arguments.Add($"STUB_CACHE_ROOT={CacheRoot}");
            arguments.Add(
                $"PATH={Path.GetDirectoryName(CopyWrapper)}:{Environment.GetEnvironmentVariable("PATH")}");
            arguments.AddRange(
            [
                PairScript,
                "--producer", Producer,
                "--lake-bin", "/bin/echo",
                "--candidate-root", Repo,
                "--candidate-output", Output,
            ]);

            return TestProcessRunner.Run(
                "env",
                arguments,
                Repo,
                TestBudgets.WorkflowProcessHangGuard,
                1024 * 1024);
        }

        internal void AddLegacyLogsToCacheEntry(string address)
        {
            var logs = Path.Combine(CacheRoot, address, "raw-lean-report.json.logs");
            Directory.CreateDirectory(logs);
            File.WriteAllText(Path.Combine(logs, "producer.log"), "legacy\n");
        }

        internal void AddDanglingLogsSymlinkToCacheEntry(string address)
        {
            var entry = Path.Combine(CacheRoot, address);
            File.CreateSymbolicLink(
                Path.Combine(entry, "raw-lean-report.json.logs"),
                Path.Combine(entry, "missing-producer-logs"));
        }

        internal bool CacheEntryHasLogs(string address)
        {
            var logs = Path.Combine(CacheRoot, address, "raw-lean-report.json.logs");
            if (Directory.Exists(logs) || File.Exists(logs)) return true;
            try
            {
                return (File.GetAttributes(logs) & FileAttributes.ReparsePoint) != 0;
            }
            catch (FileNotFoundException)
            {
                return false;
            }
        }

        internal bool LiveLogsExist() => Directory.Exists(Output + ".logs")
            && Directory.EnumerateFiles(Output + ".logs", "*", SearchOption.AllDirectories).Any();

        internal bool LiveBundleExists() => File.Exists(Output);

        internal string LiveMode()
        {
            using var provenance = System.Text.Json.JsonDocument.Parse(
                File.ReadAllText(Output + ".provenance.json"));
            return provenance.RootElement.GetProperty("mode").GetString()!;
        }

        internal string[] SnapshotLiveBundle()
        {
            var entries = new SortedDictionary<string, string>(StringComparer.Ordinal);
            foreach (var suffix in new[] { "", ".sha256", ".input.attestation", ".provenance.json" })
            {
                var path = Output + suffix;
                Assert.True(File.Exists(path), $"bundle member is missing: {path}");
                entries[suffix] = HashFile(path);
            }

            var logs = Output + ".logs";
            Assert.True(Directory.Exists(logs), $"bundle log sidecar is missing: {logs}");
            foreach (var path in Directory.EnumerateFiles(logs, "*", SearchOption.AllDirectories)
                         .Order(StringComparer.Ordinal))
            {
                entries[".logs/" + Path.GetRelativePath(logs, path)] = HashFile(path);
            }

            var materials = Output + ".materials.zip";
            Assert.True(File.Exists(materials), $"bundle material archive is missing: {materials}");
            entries[".materials.zip"] = HashFile(materials);

            return entries.Select(static pair => $"{pair.Key}={pair.Value}").ToArray();
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

        private static string HashFile(string path) =>
            Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(path))).ToLowerInvariant();

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


        private const string StubCacheEnsure = """
            #!/usr/bin/env bash
            set -euo pipefail
            printf '%s\n' 'LEAN_CACHE {"status":"seeded","method":"fake"}' >&2
            """;

        // Records each invocation, writes a byte-stable canned report + sidecar, and
        // exits 0 in well under a second. Mirrors the inspect.sh contract consumed by
        // lean-report-pair.sh: --repository <root> --output <file>.
        private const string StubProducer = """
            #!/usr/bin/env bash
            set -euo pipefail
            printf 'run\n' >> "$STUB_PRODUCER_LOG"
            if [[ -n "${STUB_PRODUCER_FAIL:-}" ]]; then
              echo "stub-producer: forced failure (no report written)" >&2
              exit 1
            fi
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
            printf '%s\n' "$STUB_REPORT_CONTENT" > "${output}.materials.zip"
            if command -v sha256sum >/dev/null 2>&1; then
              h="$(sha256sum "$output" | awk '{print $1}')"
            elif command -v openssl >/dev/null 2>&1; then
              h="$(openssl dgst -sha256 "$output" | awk '{print $NF}')"
            else
              h="$(shasum -a 256 "$output" | awk '{print $1}')"
            fi
            if [[ -n "${STUB_BAD_SHA:-}" ]]; then h="$(printf '0%.0s' {1..64})"; fi
            printf '%s  %s\n' "$h" "$(basename "$output")" > "${output}.sha256"
            rm -rf -- "${output}.logs"
            if [[ -n "${STUB_LOGS_AS_FILE:-}" ]]; then
              printf '%s\n' "$STUB_REPORT_CONTENT" > "${output}.logs"
            elif [[ -z "${STUB_OMIT_LOGS:-}" ]]; then
              mkdir -p "${output}.logs"
              if [[ -z "${STUB_EMPTY_LOGS:-}" ]]; then
                printf '%s\n' "$STUB_REPORT_CONTENT" > "${output}.logs/producer.log"
              fi
            fi
            if [[ -n "${STUB_SIDECAR_FAIL:-}" ]]; then
              mkdir "${output}.provenance.json"
            fi
            """;

        // Records each slot acquisition, then execs the wrapped worker. A cache hit
        // returns before the supervisor is ever invoked, so the slot log stays flat.
        private const string StubSupervisor = """
            #!/usr/bin/env bash
            set -euo pipefail
            printf 'slot\n' >> "$STUB_SLOT_LOG"
            if [[ -n "${STUB_SUPERVISOR_FAIL:-}" ]]; then
              echo "stub-supervisor: forced failure" >&2
              exit 71
            fi
            while [[ $# -gt 0 && "$1" != "--" ]]; do shift; done
            [[ "${1:-}" == "--" ]] && shift
            exec "$@"
            """;

        private const string StubCopy = """
            #!/usr/bin/env bash
            set -euo pipefail
            if [[ -n "${STUB_CACHE_COPY_FAIL:-}" ]]; then
              for argument in "$@"; do
                if [[ "$argument" == "$STUB_CACHE_ROOT/"* ]]; then
                  echo "stub-cp: forced cache restore failure" >&2
                  exit 86
                fi
              done
            fi
            source="${1:-}"
            destination="${@: -1}"
            /bin/cp "$@"
            if [[ -n "${STUB_INJECT_CACHED_LOGS:-}" \
              && "$source" == "$STUB_CACHE_ROOT/"* \
              && "$destination" == */raw-lean-report.json ]]; then
              mkdir -p "${destination}.logs"
              printf '%s\n' 'injected cached log' > "${destination}.logs/producer.log"
            fi
            """;
    }
}
