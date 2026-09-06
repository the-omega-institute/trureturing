using System.IO.Compression;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class JudgmentSegmentScriptTests
{
    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private sealed class JudgmentSegmentFixture : IDisposable
    {
        private const string ExecutablePath = "/usr/bin:/bin:/usr/sbin:/sbin";
        private const string BinaryAttestationSchema =
            "schema=stratalint-dotnet-binary-source-address-v1";
        internal const string ScribeSourceAddress =
            "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
        internal const string JudgeSourceAddress =
            "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";
        private static readonly UTF8Encoding Utf8NoBom = new(false, true);
        private readonly TemporaryDirectory temporary = new();
        private readonly string repository;
        private readonly string binDirectory;
        private readonly string callsPath;
        private readonly string reportCacheBundle;
        private readonly string scribeDllPath;
        private readonly string judgeDllPath;
        private readonly string expectedMergeCommit;
        private readonly string expectedTree;
        private readonly string expectedBase;
        private readonly string? expectedSourceHead;

        internal JudgmentSegmentFixture(bool createMergeCommit = false)
        {
            repository = Path.Combine(temporary.Path, "candidate");
            binDirectory = Path.Combine(temporary.Path, "bin");
            callsPath = Path.Combine(temporary.Path, "calls.log");
            reportCacheBundle = Path.Combine(
                temporary.Path, "report-cache", "raw-lean-report.json");
            scribeDllPath = Path.Combine(temporary.Path, "judge", "scribe", "scribe.dll");
            judgeDllPath = Path.Combine(temporary.Path, "judge", "cli", "judge.dll");
            ScriptHarnessScratch.EnsureDirectory(repository);
            ScriptHarnessScratch.EnsureDirectory(binDirectory);
            InstallProductionFiles();
            InstallFixtureFiles();
            InitializeRepository(createMergeCommit);
            expectedMergeCommit = GitText("rev-parse", "HEAD");
            expectedTree = GitText("rev-parse", "HEAD^{tree}");
            expectedBase = GitText("rev-parse", "HEAD^1");
            expectedSourceHead = createMergeCommit ? GitText("rev-parse", "HEAD^2") : null;
        }

        internal string ReportPath => Path.Combine(temporary.Path, "raw-lean-reports", "candidate-lean-report.json");

        internal string LeanEvidencePath =>
            Path.Combine(temporary.Path, "raw-lean-reports", "lean-inspect-segment-evidence.json");

        internal string LeanEvidenceText => File.ReadAllText(LeanEvidencePath, Utf8NoBom);

        internal string RecordedCalls =>
            File.Exists(callsPath) ? File.ReadAllText(callsPath, Utf8NoBom) : string.Empty;

        internal string ScribeDllPath => scribeDllPath;

        internal string JudgeDllPath => judgeDllPath;

        internal string ExpectedMergeCommit => expectedMergeCommit;

        internal string ExpectedTree => expectedTree;

        internal string ExpectedBase => expectedBase;

        internal string? ExpectedSourceHead => expectedSourceHead;

        internal string CanonicalReportInputAddress => "sha256:" + PairInputAddress;

        internal string RepositoryInputAddress => "sha256:" + AddressComponent;

        internal ProcessOutput RunLeanInspect(
            int scribeExitCode = 0,
            bool throughMake = false,
            string? eventName = "push",
            string? scribeSourceAddress = null) =>
            Run(
                "lean-inspect",
                scribeExitCode,
                gateExitCode: 0,
                throughMake,
                eventName,
                scribeSourceAddress ?? ScribeSourceAddress,
                JudgeSourceAddress);

        internal ProcessOutput RunAdmission(
            int gateExitCode = 0,
            bool throughMake = false,
            string? eventName = "push",
            string? judgeSourceAddress = null) =>
            Run(
                "admission",
                scribeExitCode: 0,
                gateExitCode,
                throughMake,
                eventName,
                ScribeSourceAddress,
                judgeSourceAddress ?? JudgeSourceAddress);

        internal void DeleteLeanEvidence() => File.Delete(LeanEvidencePath);

        internal void DeleteEvidenceLibrary() =>
            File.Delete(Path.Combine(repository, "tools", "scripts", "lib", "segment-evidence-lib.sh"));

        internal void TamperLeanEvidenceReportHash()
        {
            var text = LeanEvidenceText;
            using var document = JsonDocument.Parse(text);
            var current = document.RootElement.GetProperty("report_sha256").GetString()!;
            File.WriteAllText(
                LeanEvidencePath,
                text.Replace(current, new string('b', 64), StringComparison.Ordinal),
                Utf8NoBom);
        }

        internal void TamperLeanEvidenceMergeCommit()
        {
            var text = LeanEvidenceText;
            using var document = JsonDocument.Parse(text);
            var current = document.RootElement.GetProperty("merge_commit").GetString()!;
            File.WriteAllText(
                LeanEvidencePath,
                text.Replace(current, new string('e', 40), StringComparison.Ordinal),
                Utf8NoBom);
        }

        internal void WriteMalformedScribeAttestation() =>
            WriteText(scribeDllPath + ".source-address", "malformed\n");

        internal void WriteMalformedJudgeAttestation() =>
            WriteText(judgeDllPath + ".source-address", "malformed\n");

        internal void WriteMismatchedScribeAttestation() =>
            WriteBinaryAttestation(scribeDllPath, new string('a', 64));

        internal void WriteMismatchedJudgeAttestation() =>
            WriteBinaryAttestation(judgeDllPath, new string('a', 64));

        internal void WriteValidCachedReport()
        {
            WriteText(reportCacheBundle, "cached report\n");
            WriteReportSidecars(reportCacheBundle);
        }

        internal void WriteCachedReportWithDamage(string damage)
        {
            WriteText(reportCacheBundle, "cached report\n");
            WriteReportSidecars(reportCacheBundle);
            switch (damage)
            {
                case "provenance-address":
                    WriteText(
                        reportCacheBundle + ".provenance.json",
                        File.ReadAllText(reportCacheBundle + ".provenance.json", Utf8NoBom)
                            .Replace(PairInputAddress, new string('b', 64), StringComparison.Ordinal));
                    break;
                case "report-sha":
                    WriteText(
                        reportCacheBundle + ".sha256",
                        $"{new string('b', 64)}  {Path.GetFileName(reportCacheBundle)}\n");
                    break;
                case "input-attestation":
                    WriteText(
                        reportCacheBundle + ".input.attestation",
                        File.ReadAllText(reportCacheBundle + ".input.attestation", Utf8NoBom)
                            .Replace(AddressComponent, new string('b', 64), StringComparison.Ordinal));
                    break;
                case "materials-zip":
                    WriteText(reportCacheBundle + ".materials.zip", "not a zip\n");
                    break;
                default:
                    throw new ArgumentOutOfRangeException(nameof(damage), damage, null);
            }
        }

        internal void WriteValidLeanEvidenceFixture()
        {
            Directory.CreateDirectory(Path.GetDirectoryName(ReportPath)!);
            File.WriteAllText(ReportPath, "fixture report\n", Utf8NoBom);
            WriteReportSidecars(ReportPath);
            var reportHash = Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(ReportPath)));
            var merge = GitText("rev-parse", "HEAD");
            var tree = GitText("rev-parse", "HEAD^{tree}");
            var @base = GitText("rev-parse", "HEAD^1");
            var evidence = JsonSerializer.Serialize(new Dictionary<string, object?>
            {
                ["schema_version"] = "pfci-segment-evidence-v1",
                ["segment"] = "lean-inspect",
                ["event"] = "push",
                ["merge_commit"] = merge,
                ["tree"] = tree,
                ["base"] = @base,
                ["source_head"] = null,
                ["raw_rc"] = 0,
                ["outcome"] = "passed",
                ["report_input_address"] = CanonicalReportInputAddress,
                ["report_sha256"] = reportHash,
                ["judge_source_address"] = null,
                ["scribe_source_address"] = ScribeSourceAddress,
                ["selected_test_ids"] = null,
                ["ordered_check_ids"] = new[] { "produce-canonical-lean-report", "scribe-content-checks" },
            });
            File.WriteAllText(LeanEvidencePath, evidence + "\n", Utf8NoBom);
        }

        public void Dispose() => temporary.Dispose();

        private ProcessOutput Run(
            string target,
            int scribeExitCode,
            int gateExitCode,
            bool throughMake,
            string? eventName,
            string scribeSourceAddress,
            string judgeSourceAddress)
        {
            var environment = new List<string>
            {
                "-u", "GIT_CONFIG",
                "-u", "GIT_CONFIG_PARAMETERS",
                "-u", "EVENT",
                $"PATH={binDirectory}:{ExecutablePath}",
                $"TMPDIR={temporary.Path}",
                $"REPOSITORY={repository}",
                $"REPORT={ReportPath}",
                $"LEAN_INSPECT_EVIDENCE={LeanEvidencePath}",
                $"REPORT_CACHE_BUNDLE={reportCacheBundle}",
                $"REPORT_CACHE_ROOT={Path.Combine(temporary.Path, "report-delta-cache")}",
                "LAKE_BIN=/usr/bin/true",
                $"SCRIBE_DLL={scribeDllPath}",
                $"SCRIBE_SOURCE_ADDRESS={scribeSourceAddress}",
                $"JUDGE_DLL={judgeDllPath}",
                $"JUDGE_SOURCE_ADDRESS={judgeSourceAddress}",
                $"TEST_MAP_CACHE_ROOT={Path.Combine(temporary.Path, "test-map-cache")}",
                $"SCRIBE_EXIT_CODE={scribeExitCode}",
                $"GATE_EXIT_CODE={gateExitCode}",
                $"SEGMENT_CALLS={callsPath}",
                "GIT_CONFIG_GLOBAL=/dev/null",
                "GIT_CONFIG_SYSTEM=/dev/null",
                "GIT_CONFIG_NOSYSTEM=1",
            };
            if (eventName is not null)
            {
                environment.Add($"EVENT={eventName}");
            }
            if (throughMake)
            {
                environment.AddRange([
                    "/usr/bin/make", "--no-print-directory", "-C", repository, target,
                ]);
            }
            else
            {
                environment.AddRange([
                    "/bin/bash",
                    Path.Combine(repository, "tools", "scripts", "workflow", $"segment-{target}.sh"),
                ]);
            }
            return TestProcessRunner.Run(
                "/usr/bin/env",
                environment,
                repository,
                TestBudgets.ScriptProcessHangGuard,
                512 * 1024);
        }

        private void InstallProductionFiles()
        {
            WriteExecutable(
                Path.Combine(repository, "tools/scripts/workflow/segment-lean-inspect.sh"),
                TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
                    "tools/scripts/workflow/segment-lean-inspect.sh")));
            WriteExecutable(
                Path.Combine(repository, "tools/scripts/workflow/segment-admission.sh"),
                TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
                    "tools/scripts/workflow/segment-admission.sh")));
            WriteExecutable(
                Path.Combine(repository, "tools/scripts/lib/segment-evidence-lib.sh"),
                TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
                    "tools/scripts/lib/segment-evidence-lib.sh")));
            WriteExecutable(
                Path.Combine(repository, "tools/scripts/workflow/judge-content-address.sh"),
                TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
                    "tools/scripts/workflow/judge-content-address.sh")));
            WriteText(
                Path.Combine(repository, "Makefile"),
                TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create("Makefile")));
        }

        private void InstallFixtureFiles()
        {
            WriteExecutable(
                Path.Combine(repository, "tools/scripts/report/lean-report-input.sh"),
                """
                #!/usr/bin/env bash
                set -euo pipefail
                case "${1:-}" in
                  address)
                    value="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                    printf '%s %s %s %s\n' "$value" "$value" "$value" "$value"
                    ;;
                  verify)
                    report=""
                    while [[ $# -gt 0 ]]; do
                      if [[ "$1" == --report ]]; then report="$2"; shift 2; else shift; fi
                    done
                    [[ -s "$report" ]]
                    ! grep -qFx 'invalid cache' "$report"
                    ;;
                  *) exit 2 ;;
                esac
                """);
            WriteText(
                Path.Combine(repository, "tools/scripts/report/lean-report-bundle-lib.sh"),
                TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
                    "tools/scripts/report/lean-report-bundle-lib.sh")));
            WriteExecutable(
                Path.Combine(repository, "tools/scripts/report/lean-report-ci-baseline.sh"),
                """
                #!/usr/bin/env bash
                set -euo pipefail
                printf '%s\n' "${REPORT_CACHE_ROOT:?}"
                """);
            WriteExecutable(
                Path.Combine(repository, "tools/scripts/lean-report-pair.sh"),
                """
                #!/usr/bin/env bash
                set -euo pipefail
                output=""
                while [[ $# -gt 0 ]]; do
                  if [[ "$1" == --candidate-output ]]; then output="$2"; shift 2; else shift; fi
                done
                printf 'pair:%s\n' "$*" >> "${SEGMENT_CALLS:?}"
                mkdir -p "$(dirname "$output")"
                printf '%s\n' 'fixture report' > "$output"
                digest="$(sha256sum "$output" | cut -d ' ' -f 1)"
                printf '%s  %s\n' "$digest" "$(basename "$output")" > "${output}.sha256"
                value=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
                input_address=037fa3c46aeeff50a3ca2c5eb601fa6b5c2cde55aebcd18a7e2d83ac5cb40390
                printf 'schema=stratalint-lean-report-input-attestation-v1\nrepository_input_sha256=%s\nproducer_sha256=%s\nreport_sha256=%s\n' \
                  "$value" "$value" "$digest" > "${output}.input.attestation"
                printf '{"schema":"stratalint-lean-report-provenance-v1","side":"candidate","mode":"produced","source_side":"candidate","input_address":"sha256:%s","producer_sha256":"%s","repository_inspector_sha256":"%s","lean_sources_sha256":"%s","lean_config_sha256":"%s","report_sha256":"%s"}\n' \
                  "$input_address" "$value" "$value" "$value" "$value" "$digest" \
                  > "${output}.provenance.json"
                python3 - "${output}.materials.zip" <<'PY'
                import sys
                import zipfile
                with zipfile.ZipFile(sys.argv[1], "w") as archive:
                    archive.writestr("fixture.txt", "fixture\n")
                PY
                """);
            WriteExecutable(
                Path.Combine(repository, "tools/scripts/workflow/scribe-content-checks.sh"),
                """
                #!/usr/bin/env bash
                set -euo pipefail
                printf 'scribe:%s\n' "$*" >> "${SEGMENT_CALLS:?}"
                exit "${SCRIBE_EXIT_CODE:?}"
                """);
            WriteExecutable(
                Path.Combine(repository, ".github/scripts/harness-gate.sh"),
                """
                #!/usr/bin/env bash
                set -euo pipefail
                # Interface tokens consumed by the segment's fail-closed preflight:
                # --candidate-lean-report --test-map-cache-root
                printf 'gate:%s\n' "$*" >> "${SEGMENT_CALLS:?}"
                exit "${GATE_EXIT_CODE:?}"
                """);
            WriteExecutable(
                Path.Combine(repository, "tools/lean-inspector/inspect.sh"),
                "#!/usr/bin/env bash\nexit 0\n");
            WriteText(Path.Combine(repository, "tools/lean-inspector/Inspector.lean"), "def fixture := true\n");
            WriteText(Path.Combine(repository, "tools/fixture.txt"), "fixture\n");
            WriteText(Path.Combine(repository, "Blueprint/Fixture.scribe.cs"), "// fixture\n");
            WriteText(Path.Combine(repository, ".github/workflows/ci.yml"), "name: fixture\n");
            WriteText(Path.Combine(repository, "Directory.Build.props"), "<Project />\n");
            WriteText(Path.Combine(repository, "global.json"), "{}\n");
            WriteText(scribeDllPath, "scribe binary\n");
            WriteText(judgeDllPath, "judge binary\n");
            WriteBinaryAttestation(scribeDllPath, ScribeSourceAddress);
            WriteBinaryAttestation(judgeDllPath, JudgeSourceAddress);
            WriteExecutable(
                Path.Combine(binDirectory, "dotnet"),
                """
                #!/usr/bin/env bash
                set -euo pipefail
                if [[ "${1:-}" == --info ]]; then
                  printf '%s\n' 'Host:' '  Version: 10.0.0' '  Architecture: arm64'
                  exit 0
                fi
                if [[ "${1:-}" == --version ]]; then printf '%s\n' '10.0.100'; exit 0; fi
                exit 97
                """);
        }

        private void WriteBinaryAttestation(string binaryPath, string sourceAddress) =>
            WriteText(
                binaryPath + ".source-address",
                $"{BinaryAttestationSchema}\nsource_address={sourceAddress}\n");

        private static void WriteReportSidecars(string reportPath)
        {
            var digest = Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(reportPath)));
            WriteText(
                reportPath + ".sha256",
                $"{digest}  {Path.GetFileName(reportPath)}\n");
            WriteText(
                reportPath + ".input.attestation",
                "schema=stratalint-lean-report-input-attestation-v1\n"
                + $"repository_input_sha256={AddressComponent}\n"
                + $"producer_sha256={AddressComponent}\n"
                + $"report_sha256={digest}\n");
            WriteText(
                reportPath + ".provenance.json",
                $"{{\"schema\":\"stratalint-lean-report-provenance-v1\",\"side\":\"candidate\",\"mode\":\"cached\",\"source_side\":\"candidate\",\"input_address\":\"sha256:{PairInputAddress}\",\"producer_sha256\":\"{AddressComponent}\",\"repository_inspector_sha256\":\"{AddressComponent}\",\"lean_sources_sha256\":\"{AddressComponent}\",\"lean_config_sha256\":\"{AddressComponent}\",\"report_sha256\":\"{digest}\"}}\n");
            using var archive = ZipFile.Open(reportPath + ".materials.zip", ZipArchiveMode.Create);
            var entry = archive.CreateEntry("fixture.txt");
            using var writer = new StreamWriter(entry.Open(), Utf8NoBom);
            writer.Write("fixture\n");
        }

        private static string AddressComponent => new('a', 64);

        private static string PairInputAddress
        {
            get
            {
                var component = AddressComponent;
                var preimage = "schema=stratalint-lean-report-input-v1\n"
                    + $"producer_sha256={component}\n"
                    + $"repository_inspector_sha256={component}\n"
                    + $"lean_sources_sha256={component}\n"
                    + $"lean_config_sha256={component}\n";
                return Convert.ToHexStringLower(SHA256.HashData(Utf8NoBom.GetBytes(preimage)));
            }
        }

        private void InitializeRepository(bool createMergeCommit)
        {
            RunGit("init", "--quiet");
            RunGit("config", "user.email", "judgment-segments@example.invalid");
            RunGit("config", "user.name", "Judgment Segment Tests");
            RunGit("config", "commit.gpgsign", "false");
            RunGit("config", "core.hooksPath", "/dev/null");
            RunGit("add", ".");
            RunGit("commit", "--quiet", "-m", "fixture root");
            WriteText(Path.Combine(repository, "candidate-change.txt"), "candidate\n");
            RunGit("add", ".");
            RunGit("commit", "--quiet", "-m", "candidate");
            if (!createMergeCommit) return;

            var primaryBranch = GitText("branch", "--show-current");
            RunGit("checkout", "--quiet", "-b", "fixture-source", "HEAD^1");
            WriteText(Path.Combine(repository, "source-change.txt"), "source\n");
            RunGit("add", ".");
            RunGit("commit", "--quiet", "-m", "source");
            RunGit("checkout", "--quiet", primaryBranch);
            RunGit("merge", "--quiet", "--no-ff", "fixture-source", "-m", "merge");
        }

        private void RunGit(params string[] arguments)
        {
            var result = TestProcessRunner.Run(
                "/usr/bin/env",
                [
                    "-u", "GIT_CONFIG",
                    "-u", "GIT_CONFIG_PARAMETERS",
                    "GIT_CONFIG_GLOBAL=/dev/null",
                    "GIT_CONFIG_SYSTEM=/dev/null",
                    "GIT_CONFIG_NOSYSTEM=1",
                    "PATH=" + ExecutablePath,
                    "/usr/bin/git",
                    .. arguments,
                ],
                repository,
                TestBudgets.ScriptProcessHangGuard,
                64 * 1024);
            Assert.True(result.ExitCode == 0, Diagnostics(result));
        }

        private string GitText(params string[] arguments)
        {
            var result = TestProcessRunner.Run(
                "/usr/bin/git",
                arguments,
                repository,
                TestBudgets.ScriptProcessHangGuard,
                64 * 1024);
            Assert.True(result.ExitCode == 0, Diagnostics(result));
            return Encoding.UTF8.GetString(result.StandardOutput).Trim();
        }

        private static void WriteExecutable(string path, string content)
        {
            WriteText(path, content);
            File.SetUnixFileMode(
                path,
                UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        }

        private static void WriteText(string path, string content)
        {
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, content, Utf8NoBom);
        }
    }
}
