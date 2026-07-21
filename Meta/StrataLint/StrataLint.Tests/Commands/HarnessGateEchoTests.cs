using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class HarnessGateEchoTests
{
    [Fact]
    public void BaseOwnedGatePropagatesHandEditedProjectionFailure()
    {
        if (OperatingSystem.IsWindows()) return;

        var root = FindRepositoryRoot();
        using var fixture = new TemporaryDirectory();
        var fixtureRoot = PhysicalPath(fixture.Path);
        var candidate = Path.Combine(fixtureRoot, "candidate");
        var judge = Path.Combine(fixtureRoot, "judge");
        var bin = Path.Combine(fixtureRoot, "bin");
        Directory.CreateDirectory(candidate);
        Directory.CreateDirectory(judge);
        Directory.CreateDirectory(bin);
        var candidateReport = Write(candidate, "candidate-report.json", "{}\n");
        var baselineReport = Write(judge, "baseline-report.json", "{}\n");
        var judgeDll = Write(judge, "fake-judge.dll", string.Empty);
        var callLog = Path.Combine(fixtureRoot, "echo-calls.txt");
        var dotnet = Write(
            bin,
            "dotnet",
            """
            #!/usr/bin/env bash
            set -euo pipefail
            case "$1" in
              restore|build) exit 0 ;;
              msbuild) printf '%s\n' "$FAKE_JUDGE_DLL" ;;
              "$FAKE_JUDGE_DLL")
                shift
                case "$1" in
                  selftest) printf 'SELFTEST\n' ;;
                  check) exit 0 ;;
                  echo-verify)
                    printf '%s\n' "$*" >> "$ECHO_CALL_LOG"
                    printf '%s\n' 'ECHO_VERIFY_INVALID candidate block does not byte-match the derived residual summary' >&2
                    exit 1
                    ;;
                  *) exit 21 ;;
                esac
                ;;
              *) exit 22 ;;
            esac
            """ + "\n");
        File.SetUnixFileMode(
            dotnet,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);

        var result = BoundedProcessRunner.Run(
            "env",
            [
                $"PATH={bin}:{Environment.GetEnvironmentVariable("PATH")}",
                $"FAKE_JUDGE_DLL={judgeDll}",
                $"ECHO_CALL_LOG={callLog}",
                Path.Combine(root, ".github", "scripts", "harness-gate.sh"),
                "--candidate", candidate,
                "--judge-root", judge,
                "--base", "synthetic-base",
                "--candidate-lean-report", candidateReport,
                "--baseline-lean-report", baselineReport,
            ],
            root,
            TimeSpan.FromSeconds(30),
            64 * 1024);

        Assert.True(
            result.ExitCode == 1,
            $"gate exited {result.ExitCode}: {Encoding.UTF8.GetString(result.StandardError)}");
        Assert.Equal("echo-verify --base synthetic-base --if-affected\n", File.ReadAllText(callLog));
        Assert.Contains(
            "ECHO_VERIFY_INVALID candidate block does not byte-match",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    private static string Write(string directory, string name, string contents)
    {
        var path = Path.Combine(directory, name);
        File.WriteAllText(path, contents, new UTF8Encoding(false));
        return path;
    }

    private static string PhysicalPath(string path)
    {
        var result = BoundedProcessRunner.Run(
            "/bin/pwd",
            ["-P"],
            path,
            TimeSpan.FromSeconds(5),
            4096);
        Assert.Equal(0, result.ExitCode);
        return Encoding.UTF8.GetString(result.StandardOutput).Trim();
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, ".github", "scripts", "harness-gate.sh")))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException("Could not locate repository harness gate.");
    }
}
