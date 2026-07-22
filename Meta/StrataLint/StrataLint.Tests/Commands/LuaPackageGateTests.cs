using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LuaPackageGateTests
{
    [Fact]
    public void GateRunsOnlyWorkspaceDeclaredPackages()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new LuaGateFixture(
            "packages/alpha",
            "packages/beta");
        fixture.AddPackage("alpha");
        fixture.AddPackage("beta");
        fixture.AddPackage("undeclared");

        var result = fixture.Run("pass");
        var log = File.ReadAllText(fixture.InvocationLog);

        Assert.Equal(0, result.ExitCode);
        Assert.Contains("/packages/alpha", log, StringComparison.Ordinal);
        Assert.Contains("/packages/beta", log, StringComparison.Ordinal);
        Assert.DoesNotContain("/packages/undeclared", log, StringComparison.Ordinal);
        Assert.Equal(2, log.Split("=== invocation ===", StringSplitOptions.None).Length - 1);
    }

    [Fact]
    public void GateRejectsPackageWithZeroDiscoveredTests()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new LuaGateFixture("packages/alpha");
        fixture.AddPackage("alpha");

        var result = fixture.Run("empty");
        var error = Encoding.UTF8.GetString(result.StandardError);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("alpha", error, StringComparison.Ordinal);
        Assert.Contains("zero tests", error, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void GatePropagatesFrameworkFailure()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new LuaGateFixture("packages/alpha");
        fixture.AddPackage("alpha");

        var result = fixture.Run("fail");

        Assert.Equal(17, result.ExitCode);
    }

    private sealed class LuaGateFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        private readonly string fakeFramework;
        private readonly string runScript;

        internal LuaGateFixture(params string[] units)
        {
            var root = FindRepositoryRoot();
            var fkst = Path.Combine(temporary.Path, ".fkst");
            var scripts = Path.Combine(fkst, "scripts");
            Directory.CreateDirectory(scripts);
            runScript = Path.Combine(scripts, "run.sh");
            File.Copy(Path.Combine(root, ".fkst", "scripts", "run.sh"), runScript);
            File.WriteAllText(
                Path.Combine(fkst, "fkst.workspace.toml"),
                "[workspace]\nunits = ["
                + string.Join(", ", units.Select(unit => $"\"{unit}\""))
                + "]\n",
                new UTF8Encoding(false));

            InvocationLog = Path.Combine(temporary.Path, "framework.log");
            fakeFramework = Path.Combine(temporary.Path, "fkst-framework");
            File.WriteAllText(
                fakeFramework,
                """
                #!/usr/bin/env bash
                set -euo pipefail
                printf '%s\n' '=== invocation ===' "$@" >> "$FAKE_FRAMEWORK_LOG"
                if [[ "$FAKE_FRAMEWORK_MODE" == fail ]]; then
                  exit 17
                fi
                report=""
                while [[ $# -gt 0 ]]; do
                  if [[ "$1" == --report-json ]]; then
                    report="$2"
                    break
                  fi
                  shift
                done
                [[ -n "$report" ]]
                if [[ "$FAKE_FRAMEWORK_MODE" == empty ]]; then
                  printf '%s\n' '{"schema":"fkst.test.report.v1","summary":{"passed":0,"failed":0},"tests":[]}' > "$report"
                else
                  printf '%s\n' '{"schema":"fkst.test.report.v1","summary":{"passed":1,"failed":0},"tests":[{"status":"pass"}]}' > "$report"
                fi
                """ + "\n",
                new UTF8Encoding(false));
            if (!OperatingSystem.IsWindows())
            {
                File.SetUnixFileMode(
                    fakeFramework,
                    UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
            }
        }

        internal string InvocationLog { get; }

        internal void AddPackage(string name)
        {
            var package = Path.Combine(temporary.Path, "packages", name);
            Directory.CreateDirectory(Path.Combine(package, "tests"));
            File.WriteAllText(
                Path.Combine(package, "fkst.toml"),
                $"kind = \"package\"\nname = \"{name}\"\npersistence_class = \"stateless_adapter\"\n[code]\nroot = \".\"\n",
                new UTF8Encoding(false));
            File.WriteAllText(
                Path.Combine(package, "tests", "smoke_test.lua"),
                "return { test_smoke = function() end }\n",
                new UTF8Encoding(false));
        }

        internal ProcessOutput Run(string mode) => BoundedProcessRunner.Run(
            "env",
            [
                $"BIN={fakeFramework}",
                $"FAKE_FRAMEWORK_LOG={InvocationLog}",
                $"FAKE_FRAMEWORK_MODE={mode}",
                "/bin/bash",
                runScript,
                "test",
            ],
            temporary.Path,
            TimeSpan.FromSeconds(30),
            64 * 1024);

        public void Dispose() => temporary.Dispose();

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
    }
}
