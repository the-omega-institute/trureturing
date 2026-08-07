using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    [Theory]
    [InlineData("pass", 0)]
    [InlineData("semantic-test", 41)]
    [InlineData("semantic-gate", 42)]
    [InlineData("configuration", 78)]
    [InlineData("toolchain-missing", 127)]
    [InlineData("timeout", 124)]
    [InlineData("signal-term", 143)]
    [InlineData("exit-126", 126)]
    [InlineData("exit-127", 127)]
    [InlineData("unknown-dotnet", 73)]
    [InlineData("unknown", 73)]
    [InlineData("starved-lean-slot", 2)]
    public void PreflightPreservesExitCode(string scenario, int expectedExitCode)
    {
        if (OperatingSystem.IsWindows()) return;

        var root = FindRepositoryRoot();
        using var fixture = new TemporaryDirectory();
        var binDirectory = Path.Combine(fixture.Path, "bin");
        Directory.CreateDirectory(binDirectory);
        WriteExecutable(
            Path.Combine(binDirectory, "git"),
            """
            #!/usr/bin/env bash
            if [[ "${PREFLIGHT_SCENARIO:-}" == configuration && "$*" == "rev-parse --show-toplevel" ]]; then
              exit 78
            fi
            exec /usr/bin/git "$@"
            """);
        WriteExecutable(
            Path.Combine(binDirectory, "dotnet"),
            """
            #!/usr/bin/env bash
            if [[ "${1:-}" == --version ]]; then
              [[ "${PREFLIGHT_SCENARIO:-}" != toolchain-missing ]] || exit 127
              exit 0
            fi
            if [[ "${1:-}" == build ]]; then exit 1; fi
            if [[ "${1:-}" == msbuild ]]; then exit 1; fi
            exit 0
            """);
        WriteExecutable(
            Path.Combine(binDirectory, "lake"),
            """
            #!/usr/bin/env bash
            [[ "${1:-}" == --version ]] || exit 64
            exit 0
            """);
        WriteExecutable(
            Path.Combine(binDirectory, "make"),
            """
            #!/usr/bin/env bash
            target="${1:-}"
            case "${PREFLIGHT_SCENARIO:-}:$target" in
              semantic-test:test) exit 41 ;;
              semantic-gate:gate) exit 42 ;;
              timeout:lean-report) exit 124 ;;
              signal-term:lean-report) kill -TERM "$PPID"; exit 0 ;;
              exit-126:lean-report) exit 126 ;;
              exit-127:lean-report) exit 127 ;;
              unknown-dotnet:dotnet) exit 73 ;;
              unknown:lean-report) exit 73 ;;
              starved-lean-slot:lean-report) exit 2 ;;
            esac
            exit 0
            """);

        var result = BoundedProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "PREFLIGHT_SCENARIO=\"$1\" BASE=HEAD^ PATH=\"$2:/usr/bin:/bin\" exec /bin/bash \"$3\"",
                "preflight-contract",
                scenario,
                binDirectory,
                Path.Combine(root, PreflightScriptPath),
            ],
            root,
            TimeSpan.FromSeconds(30),
            64 * 1024);

        Assert.Equal(expectedExitCode, result.ExitCode);
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void WriteExecutable(string path, string content)
    {
        File.WriteAllText(path, content + "\n");
        File.SetUnixFileMode(
            path,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
    }
}
