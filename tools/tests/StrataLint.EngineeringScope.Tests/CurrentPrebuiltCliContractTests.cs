using System.Text.Json;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class CurrentPrebuiltCliContractTests
{
    [Theory]
    [InlineData("bound", null, null)]
    [InlineData("bound", "321", "654")]
    [InlineData("changed-dll", null, null)]
    [InlineData("changed-producer-dll", null, null)]
    [InlineData("changed-source", null, null)]
    public void CurrentHandsOnlyValidatedCliToProducerWithoutRepeatingEngineering(string scenario, string? buildBudget, string? lockBudget)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TemporaryFileSystem.Directory.CreateTempSubdirectory("current-prebuilt-").FullName;
        var originalPath = Environment.GetEnvironmentVariable("PATH");
        var originalDeadline = Environment.GetEnvironmentVariable("PREFLIGHT_DEADLINE_AT");
        var originalBuildBudget = Environment.GetEnvironmentVariable("STRATALINT_BUILD_TIMEOUT_SECONDS");
        var originalLockBudget = Environment.GetEnvironmentVariable("STRATALINT_LOCK_TIMEOUT_SECONDS");
        try
        {
            const string project = "tools/tests/Probe/Probe.csproj";
            Write(project, "<Project><PropertyGroup><IsTestProject>true</IsTestProject></PropertyGroup></Project>\n");
            WriteExecutable("build/bin/git", """
                case "$*" in
                  'ls-files --stage -z') printf '100644 0000000000000000000000000000000000000000 0\ttools/tests/Probe/Probe.csproj\0' ;;
                  'ls-files --others --exclude-standard -z') ;;
                  *) exit 97 ;;
                esac
                """);
            WriteExecutable("build/bin/make", """
                [[ "$*" == '--no-print-directory lean-report' ]] || exit 91
                [[ "${STRATALINT_LEAN_PRODUCER_DLL:-}" -ef "$PWD/tools/StrataLint.Lean/bin/Release/net10.0/StrataLint.Lean.dll" ]] || exit 92
                [[ -f "$STRATALINT_LEAN_PRODUCER_DLL" ]] || exit 93
                printf 'validated-cli\n' > build/producer.log
                printf '%s\n' "${STRATALINT_BUILD_TIMEOUT_SECONDS:-unset}" > build/producer-budget
                printf '%s\n' "${STRATALINT_LOCK_TIMEOUT_SECONDS:-unset}" > build/producer-lock-budget
                printf '%s\n' "${STRATALINT_LEAN_REPORT_LOG_DIR:-unset}" > build/producer-log-dir
                exit 23
                """);
            WriteExecutable("build/bin/dotnet", "printf 'unexpected-common-work\n' >> build/repeated.log\nexit 94");
            Environment.SetEnvironmentVariable("PATH", Path.Combine(root, "build/bin") + Path.PathSeparator + originalPath);
            Environment.SetEnvironmentVariable("PREFLIGHT_DEADLINE_AT", null);
            Environment.SetEnvironmentVariable("STRATALINT_BUILD_TIMEOUT_SECONDS", buildBudget);
            Environment.SetEnvironmentVariable("STRATALINT_LOCK_TIMEOUT_SECONDS", lockBudget);
            var binaries = new[] { CommonExecutionEvidence.CliPath, CommonExecutionEvidence.ScribePath,
                CommonExecutionEvidence.RunnerPath, CommonExecutionEvidence.LeanProducerPath };
            foreach (var binary in binaries) Write(binary, "synthetic candidate binary");
            Write("build/engineering.log", "synthetic engineering fixture\n");
            var candidate = CommonExecutionEvidence.Candidate(root);
            CommonExecutionEvidence.SealBuild(root, candidate, binaries, CommonExecutionEvidence.BuildSteps
                .Select(name => new StageStep(name, 0, 0, "executed", "build/engineering.log")).ToArray());
            var before = CommonExecutionEvidence.Hash(Path.Combine(root, CommonExecutionEvidence.BuildPath));
            Write("build/ci/logs/current/lean-inspector/stale.exit.log", "0\n");
            if (scenario == "changed-dll") Write(CommonExecutionEvidence.CliPath, "changed binary");
            if (scenario == "changed-producer-dll") Write(CommonExecutionEvidence.LeanProducerPath, "changed producer binary");
            if (scenario == "changed-source") Write(project, "<Project />");

            using var output = new StringWriter();
            Assert.Equal(2, new CommonStages(root, output).Run("current", null));

            using var summary = JsonDocument.Parse(TemporaryFileSystem.File.ReadAllText(
                Path.Combine(root, CommonExecutionEvidence.RootPath, "current-result.json")));
            if (scenario == "bound")
            {
                var step = Assert.Single(summary.RootElement.GetProperty("steps").EnumerateArray());
                Assert.Equal("lean-report", step.GetProperty("name").GetString());
                Assert.Equal(23, step.GetProperty("raw_exit").GetInt32());
                Assert.Equal("validated-cli\n", TemporaryFileSystem.File.ReadAllText(Path.Combine(root, "build/producer.log")));
                Assert.Equal((buildBudget ?? "21600") + "\n", TemporaryFileSystem.File.ReadAllText(Path.Combine(root, "build/producer-budget")));
                Assert.Equal((lockBudget ?? "21600") + "\n", TemporaryFileSystem.File.ReadAllText(Path.Combine(root, "build/producer-lock-budget")));
                Assert.Equal(Path.Combine(root, "build/ci/logs/current/lean-inspector") + "\n",
                    TemporaryFileSystem.File.ReadAllText(Path.Combine(root, "build/producer-log-dir")));
                Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, "build/ci/logs/current/lean-inspector/stale.exit.log")));
            }
            else
            {
                Assert.Empty(summary.RootElement.GetProperty("steps").EnumerateArray());
                Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, "build/producer.log")));
            }
            Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, CommonExecutionEvidence.TestsPath)));
            Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, CommonExecutionEvidence.EngineeringPath)));
            Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, "build/repeated.log")));
            Assert.Equal(before, CommonExecutionEvidence.Hash(Path.Combine(root, CommonExecutionEvidence.BuildPath)));

            void Write(string path, string text)
            {
                var full = Path.Combine(root, path);
                TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(full)!);
                TemporaryFileSystem.File.WriteAllText(full, text);
            }

            void WriteExecutable(string path, string body)
            {
                Write(path, "#!/bin/bash\nset -euo pipefail\n" + body + "\n");
                File.SetUnixFileMode(Path.Combine(root, path), UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
            }
        }
        finally
        {
            Environment.SetEnvironmentVariable("PATH", originalPath);
            Environment.SetEnvironmentVariable("PREFLIGHT_DEADLINE_AT", originalDeadline);
            Environment.SetEnvironmentVariable("STRATALINT_BUILD_TIMEOUT_SECONDS", originalBuildBudget);
            Environment.SetEnvironmentVariable("STRATALINT_LOCK_TIMEOUT_SECONDS", originalLockBudget);
            TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }
}
