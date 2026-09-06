using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using FixtureFile = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

public sealed class LeanCacheInputScriptTests
{
    [Fact]
    public void AddressSurvivesReportHelperFailure()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanInputFixture();

        var result = fixture.RunPublisher("address");

        fixture.AssertIndependentSuccess(result);
        Assert.Contains($"sources_sha256={fixture.ExpectedSources}", result.Text, StringComparison.Ordinal);
        Assert.Contains($"config_sha256={fixture.ExpectedConfig}", result.Text, StringComparison.Ordinal);
        Assert.Contains($"tag={fixture.Tag}", result.Text, StringComparison.Ordinal);
    }

    [Fact]
    public void FetchSurvivesReportHelperFailure()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanInputFixture();

        var result = fixture.RunPublisher("fetch");

        fixture.AssertIndependentSuccess(result);
        Assert.Contains("\"status\":\"unpacked\"", result.Text, StringComparison.Ordinal);
        Assert.Equal(new[] { "unpack" }, fixture.LakeCalls);
    }

    [Fact]
    public void PublishSurvivesReportHelperFailure()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanInputFixture();

        var result = fixture.RunPublisher("publish");

        fixture.AssertIndependentSuccess(result);
        Assert.Contains("\"status\":\"published\"", result.Text, StringComparison.Ordinal);
        Assert.Equal(new[] { "pack" }, fixture.LakeCalls);
        Assert.Contains($"sources_sha256={fixture.ExpectedSources}\n", fixture.PublishedManifest, StringComparison.Ordinal);
        Assert.Contains($"config_sha256={fixture.ExpectedConfig}\n", fixture.PublishedManifest, StringComparison.Ordinal);
        Assert.Contains($"producer_commit_sha={LeanInputFixture.ProducerSha}\n", fixture.PublishedManifest, StringComparison.Ordinal);
    }

    [Fact]
    public void ReportOnlyChangeKeepsLeanInputAddresses()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanInputFixture();
        var before = fixture.ReadAddresses();

        fixture.Write("tools/lean-inspector/inspect.sh", "#!/bin/bash\nexit 99\n");
        fixture.Write("tools/lean-inspector/delta.py", "raise RuntimeError('report only')\n");
        fixture.Write("tools/StrataLint.Engine/CanonicalWriter.cs", "// changed report writer\n");

        Assert.Equal(before, fixture.ReadAddresses());
        Assert.Equal($"{fixture.ExpectedSources} {fixture.ExpectedConfig}\n", before);
    }

    [Fact]
    public void LeanSourceChangeChangesOnlySourcesAddress()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanInputFixture();
        var before = fixture.ReadAddresses().TrimEnd().Split(' ');

        fixture.Write("D5/Zeta.lean", "theorem changed : True := by trivial\n");
        var after = fixture.ReadAddresses().TrimEnd().Split(' ');

        Assert.NotEqual(before[0], after[0]);
        Assert.Equal(before[1], after[1]);
        Assert.Equal(fixture.ExpectedSources, after[0]);
    }

    [Fact]
    public void LeanConfigChangeChangesConfigAddress()
    {
        if (OperatingSystem.IsWindows()) return;
        foreach (var path in new[] { "lean-toolchain", "lake-manifest.json", "lakefile.toml", "lakefile.lean" })
        {
            using var fixture = new LeanInputFixture();
            var before = fixture.ReadAddresses().TrimEnd().Split(' ');
            fixture.Write(path, fixture.Inputs[path] + "\n");
            var after = fixture.ReadAddresses().TrimEnd().Split(' ');

            Assert.Equal(before[0], after[0]);
            Assert.NotEqual(before[1], after[1]);
            Assert.Equal(fixture.ExpectedConfig, after[1]);
        }
    }

    [Fact]
    public void MissingLeanInputFailsClosed()
    {
        if (OperatingSystem.IsWindows()) return;
        foreach (var path in new[] { "Trureturing.lean", "lean-toolchain", "lake-manifest.json", "lakefiles", "D5" })
        {
            using var fixture = new LeanInputFixture();
            fixture.ReadAddresses();
            fixture.RemoveInput(path);

            var result = fixture.RunLeaf();

            Assert.NotEqual(0, result.ExitCode);
            Assert.Equal(string.Empty, result.Output);
        }
    }

    [Fact]
    public void ExistingLeanInputAddressesStayByteIdentical()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanInputFixture();

        Assert.Equal(
            Encoding.ASCII.GetBytes($"{fixture.ExpectedSources} {fixture.ExpectedConfig}\n"),
            Encoding.ASCII.GetBytes(fixture.ReadAddresses()));
    }

    [Fact]
    public void LeanInspectorDefaultTargetRemainsASourceInput()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanInputFixture();
        var before = fixture.ReadAddresses().TrimEnd().Split(' ');

        fixture.Write("tools/lean-inspector/LeanInformationAudit.lean", "def audit := 2\n");
        var after = fixture.ReadAddresses().TrimEnd().Split(' ');

        Assert.NotEqual(before[0], after[0]);
        Assert.Equal(before[1], after[1]);
        Assert.Equal(fixture.ExpectedSources, after[0]);
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private sealed class LeanInputFixture : IDisposable
    {
        internal const string ProducerSha = "0123456789abcdef0123456789abcdef01234567";
        private const string LeafPath = "tools/scripts/worktree/lean-cache-input.sh";
        private const string PublisherPath = "tools/scripts/worktree/lean-cache-publish.sh";
        private readonly TemporaryDirectory temporary = new();
        private readonly string repository;
        private readonly string bin;
        private readonly string candidateLeaf;
        private readonly string reportCalls;
        private readonly string lakeCalls;
        private readonly string payload;
        private readonly string publishedManifest;

        internal LeanInputFixture()
        {
            repository = Path.Combine(temporary.Path, "repository");
            bin = Path.Combine(temporary.Path, "bin");
            payload = Path.Combine(temporary.Path, "payload");
            reportCalls = Path.Combine(temporary.Path, "report.calls");
            lakeCalls = Path.Combine(temporary.Path, "lake.calls");
            publishedManifest = Path.Combine(temporary.Path, "published.manifest");
            candidateLeaf = Path.Combine(TestRepositoryLayout.FindRoot(), LeafPath);
            foreach (var directory in new[] { repository, bin, payload, Path.Combine(repository, ".lake/build") })
                ScriptHarnessScratch.EnsureDirectory(directory);
            Write("Trureturing.lean", "import D5.Zeta\n");
            Write("D5/Zeta.lean", "theorem zeta : True := by trivial\n");
            Write("D5/Alpha/Nested.lean", "def nested := 1\n");
            Write("tools/lean-inspector/LeanInformationAudit.lean", "def audit := 1\n");
            Write("tools/lean-inspector/Inspector.lean", "def inspector := 0\n");
            Write("lean-toolchain", "leanprover/lean4:v4.31.0\n");
            Write("lake-manifest.json", "{\"version\":\"1.1.0\"}\n");
            Write("lakefile.toml", "name = \"fixture\"\n");
            Write("lakefile.lean", "import Lake\n");
            Write("tools/lean-inspector/inspect.sh", "#!/bin/bash\n");
            Write("tools/lean-inspector/delta.py", "# report only\n");
            Write("tools/StrataLint.Engine/CanonicalWriter.cs", "// report only\n");
            ScriptHarnessScratch.CopyScriptInto(
                Path.Combine(TestRepositoryLayout.FindRoot(), PublisherPath), Path.Combine(repository, PublisherPath));
            WriteStub(Path.Combine(repository, LeafPath), "exec /bin/bash \"$LEAN_INPUT_CANDIDATE\" \"$@\"");
            WriteStub(Path.Combine(repository, "tools/scripts/report/lean-report-input.sh"),
                "printf 'called\\n' >> \"$LEAN_INPUT_REPORT_CALLS\"\nexit 73");
            WriteStub(Path.Combine(bin, "dotnet"), "printf 'unexpected MSBuild call\\n' >&2\nexit 74");
            WriteStub(Path.Combine(bin, "lake"), """
                printf '%s\n' "$1" >> "$LEAN_INPUT_LAKE_CALLS"
                case "$1" in
                  pack) cp "$LEAN_INPUT_PAYLOAD/lean-build.tgz" "$2" ;;
                  unpack) cmp "$2" "$LEAN_INPUT_PAYLOAD/lean-build.tgz" ;;
                  *) exit 75 ;;
                esac
                """);
            ScriptHarnessScratch.WriteScratchText(Path.Combine(payload, "lean-build.tgz"), "fixture archive\n");
            var archiveSha = Hash("fixture archive\n");
            ScriptHarnessScratch.WriteScratchText(Path.Combine(payload, "manifest.txt"),
                $"toolchain=leanprover/lean4:v4.31.0\nconfig_sha256={ExpectedConfig}\nsources_sha256={ExpectedSources}\n"
                + $"archive_sha256={archiveSha}\nproducer_commit_sha={ProducerSha}\nworkflow_run_id=4242\n");
            ScriptHarnessScratch.WriteScratchText(Path.Combine(payload, "release.json"), JsonSerializer.Serialize(new
            {
                target_commitish = ProducerSha,
                assets = new[]
                {
                    new { name = "lean-build.tgz", digest = "sha256:" + archiveSha },
                    new { name = "manifest.txt", digest = "sha256:" + Hash(FixtureFile.ReadAllText(Path.Combine(payload, "manifest.txt"))) },
                },
            }));
            WriteStub(Path.Combine(bin, "gh"), """
                case "$1 $2" in
                  'release view') exit 1 ;;
                  'release download')
                    [[ "$3" == "$LEAN_INPUT_TAG" ]] || exit 76
                    shift 3
                    destination=''
                    while [[ $# -gt 0 ]]; do
                      case "$1" in
                        --dir) destination="$2"; shift 2 ;;
                        --repo|--pattern) shift 2 ;;
                        *) exit 77 ;;
                      esac
                    done
                    [[ -n "$destination" ]] || exit 78
                    cp "$LEAN_INPUT_PAYLOAD/lean-build.tgz" "$LEAN_INPUT_PAYLOAD/manifest.txt" "$destination/"
                    ;;
                  'release create')
                    [[ "$3" == "$LEAN_INPUT_TAG" ]] || exit 79
                    shift 3
                    target=''
                    while [[ $# -gt 0 ]]; do
                      case "$1" in
                        --target) target="$2"; shift 2 ;;
                        --repo|--title|--notes) shift 2 ;;
                        --latest=false) shift ;;
                        */manifest.txt) cp "$1" "$LEAN_INPUT_PUBLISHED_MANIFEST"; shift ;;
                        */lean-build.tgz) cmp "$1" "$LEAN_INPUT_PAYLOAD/lean-build.tgz"; shift ;;
                        *) exit 80 ;;
                      esac
                    done
                    [[ "$target" == "$GITHUB_SHA" ]]
                    ;;
                  "api repos/fixture/lean-cache/releases/tags/$LEAN_INPUT_TAG") cat "$LEAN_INPUT_PAYLOAD/release.json" ;;
                  *) exit 81 ;;
                esac
                """);
        }

        internal Dictionary<string, string> Inputs { get; } = new(StringComparer.Ordinal);
        // Independent v1 preimages: root first, then each source family in byte order;
        // config follows the declared toolchain, manifest, TOML, Lean order.
        internal string ExpectedSources => HashManifest(new[] { "Trureturing.lean" }
            .Concat(Inputs.Keys.Where(path => path.StartsWith("D5/", StringComparison.Ordinal) && path.EndsWith(".lean", StringComparison.Ordinal)).Order(StringComparer.Ordinal))
            .Concat(Inputs.Keys.Where(path => path.StartsWith("tools/lean-inspector/", StringComparison.Ordinal) && path.EndsWith(".lean", StringComparison.Ordinal)).Order(StringComparer.Ordinal)));
        internal string ExpectedConfig => HashManifest(["lean-toolchain", "lake-manifest.json", "lakefile.toml", "lakefile.lean"]);
        internal string Tag => $"lean-cache-v1-leanprover-lean4-v4-31-0-{ExpectedConfig[..16]}-{ExpectedSources[..16]}";
        internal string[] LakeCalls => ScriptHarnessScratch.ReadRecordedCalls(lakeCalls);
        internal string PublishedManifest => FixtureFile.ReadAllText(publishedManifest);

        internal void Write(string path, string text)
        {
            Inputs[path] = text;
            var absolute = Path.Combine(repository, path);
            ScriptHarnessScratch.EnsureDirectory(Path.GetDirectoryName(absolute)!);
            ScriptHarnessScratch.WriteScratchText(absolute, text);
        }

        internal void RemoveInput(string path)
        {
            if (path == "D5")
            {
                var result = Run("/bin/mv", Path.Combine(repository, "D5"), Path.Combine(repository, "absent-D5"));
                Assert.Equal(0, result.ExitCode);
                return;
            }
            foreach (var relative in path == "lakefiles" ? new[] { "lakefile.toml", "lakefile.lean" } : new[] { path })
                ScriptHarnessScratch.DeleteScratchFile(Path.Combine(repository, relative));
        }

        internal Attempt RunLeaf() => Run("/bin/bash", candidateLeaf, "address", "--repository", repository);
        internal Attempt RunPublisher(string verb) => Run("/bin/bash", Path.Combine(repository, PublisherPath), verb, "--repository", repository);

        internal string ReadAddresses()
        {
            var result = RunLeaf();
            AssertIndependentSuccess(result);
            Assert.Matches("^[0-9a-f]{64} [0-9a-f]{64}\n$", result.Output);
            return result.Output;
        }

        internal void AssertIndependentSuccess(Attempt result)
        {
            var calls = ScriptHarnessScratch.ReadRecordedCalls(reportCalls);
            Assert.True(result.ExitCode == 0 && calls.Length == 0,
                $"exit={result.ExitCode}; report_helper_calls={calls.Length}\n{result.Text}");
        }

        private Attempt Run(params string[] arguments)
        {
            var process = TestProcessRunner.Run("/usr/bin/env",
                new[]
                {
                    $"PATH={bin}:{Environment.GetEnvironmentVariable("PATH")}",
                    $"LEAN_INPUT_CANDIDATE={candidateLeaf}",
                    $"LEAN_INPUT_REPORT_CALLS={reportCalls}",
                    $"LEAN_INPUT_LAKE_CALLS={lakeCalls}",
                    $"LEAN_INPUT_PAYLOAD={payload}",
                    $"LEAN_INPUT_PUBLISHED_MANIFEST={publishedManifest}",
                    $"LEAN_INPUT_TAG={Tag}",
                    $"STRATALINT_LEAN_INPUT_MEMO_ROOT={temporary.Path}/memo",
                    "STRATALINT_CACHE_REPO=fixture/lean-cache",
                    $"GITHUB_SHA={ProducerSha}",
                    "GITHUB_RUN_ID=4242",
                }.Concat(arguments).ToArray(), repository, TestBudgets.ScriptProcessHangGuard, 64 * 1024);
            return new Attempt(process.ExitCode, Encoding.UTF8.GetString(process.StandardOutput), Encoding.UTF8.GetString(process.StandardError));
        }

        private string HashManifest(IEnumerable<string> paths) => Hash(string.Concat(paths.Select(path => $"{Hash(Inputs[path])}  {path}\n")));
        private static string Hash(string value) => Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(value)));
        private static void WriteStub(string path, string body)
        {
            ScriptHarnessScratch.EnsureDirectory(Path.GetDirectoryName(path)!);
            ScriptHarnessScratch.WriteExecutableStub(path, body);
        }

        public void Dispose() => temporary.Dispose();
    }

    private sealed record Attempt(int ExitCode, string Output, string Error)
    {
        internal string Text => Output + Error;
    }
}
