using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    [Theory]
    [InlineData("pass", 0, "PASS:NONE")]
    [InlineData("semantic-test", 41, "FAIL:SEMANTIC")]
    [InlineData("semantic-gate", 42, "FAIL:SEMANTIC")]
    [InlineData("configuration", 78, "FAIL:CONFIGURATION")]
    [InlineData("toolchain-missing", 127, "FAIL:TOOLCHAIN")]
    [InlineData("timeout", 124, "FAIL:INFRASTRUCTURE")]
    [InlineData("signal-term", 143, "FAIL:INFRASTRUCTURE")]
    [InlineData("exit-126", 126, "FAIL:TOOLCHAIN")]
    [InlineData("exit-127", 127, "FAIL:TOOLCHAIN")]
    [InlineData("unknown-dotnet", 73, "UNKNOWN:UNKNOWN")]
    [InlineData("unknown", 73, "UNKNOWN:UNKNOWN")]
    [InlineData("starved-lean-slot", 2, "UNKNOWN:UNKNOWN")]
    public void PreflightPreservesExitCode(
        string scenario,
        int expectedExitCode,
        string expectedDeclaration)
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
              semantic-test:tools-test) exit 41 ;;
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
        Assert.EndsWith(
            $"FKST_LOCAL_ITERATION_RESULT:v2:{expectedDeclaration}\n",
            System.Text.Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
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
