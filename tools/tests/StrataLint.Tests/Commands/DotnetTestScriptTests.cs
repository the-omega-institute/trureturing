using System.Text;
using System.Text.Json;
using System.Xml.Linq;
using static StrataLint.TestSupport.TestExecutable;

namespace StrataLint.Tests;

public sealed class DotnetTestScriptTests
{
    [Theory]
    [InlineData("project", "selected", false, 0)]
    [InlineData("relative-project", "selected", false, 0)]
    [InlineData("project", "other", false, 2)]
    [InlineData("project", "selected", true, 0)]
    [InlineData("project", "other", true, 2)]
    [InlineData("unknown", "all-owners", false, 2)]
    [InlineData("unknown", "all-owners", true, 2)]
    [InlineData("outside", "all-owners", false, 2)]
    [InlineData("production", "all-owners", true, 2)]
    [InlineData("solution", "all-owners", false, 0)]
    [InlineData("solution", "selected", false, 2)]
    [InlineData("solution", "selected", true, 0)]
    [InlineData("solution", "zero", true, 2)]
    public void DotnetTestBindsEvidenceToTheExplicitRegisteredTarget(string scope, string evidence, bool filtered, int expectedExit)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        const string selectedProject = "tools/tests/StrataLint.EngineeringScope.Tests/StrataLint.EngineeringScope.Tests.csproj";
        using var registration = JsonDocument.Parse(File.ReadAllText(Path.Combine(root, "Meta/engineering-projects.json")));
        var projects = registration.RootElement.GetProperty("projects").EnumerateArray().ToArray();
        var selectedAssembly = projects.Single(project => project.GetProperty("path").GetString() == selectedProject)
            .GetProperty("assembly").GetString()!;
        var owners = projects.Where(project => project.GetProperty("role").GetString() == "owned-test")
            .Select(project => project.GetProperty("assembly").GetString()!).Order(StringComparer.Ordinal).ToArray();
        var otherAssembly = owners.First(assembly => assembly != selectedAssembly);
        var emitted = evidence switch
        {
            "all-owners" => owners,
            "selected" => [selectedAssembly],
            "other" => new[] { otherAssembly },
            "zero" => [],
            _ => throw new ArgumentException("unknown fixture evidence", nameof(evidence)),
        };
        using var fixture = new TemporaryDirectory();
        var binDirectory = Path.Combine(fixture.Path, "bin");
        var trx = Path.Combine(fixture.Path, "fixture.trx");
        var log = Path.Combine(fixture.Path, "dotnet.log");
        Directory.CreateDirectory(binDirectory);
        new XDocument(new XElement("TestRun",
            new XElement("Results", emitted.Select((assembly, index) => new XElement("UnitTestResult",
                new XAttribute("testId", index), new XAttribute("testName", assembly + ".Runs"), new XAttribute("outcome", "Passed")))),
            new XElement("TestDefinitions", emitted.Select((assembly, index) => new XElement("UnitTest",
                new XAttribute("id", index), new XAttribute("storage", assembly + ".dll"),
                new XElement("TestMethod", new XAttribute("className", assembly + ".Fixture"), new XAttribute("name", "Runs"))))),
            new XElement("ResultSummary", new XAttribute("outcome", "Completed"), new XElement("Counters",
                new XAttribute("executed", emitted.Length), new XAttribute("passed", emitted.Length))))).Save(trx);
        WriteExecutable(Path.Combine(binDirectory, "dotnet"),
            """
            #!/bin/bash
            set -euo pipefail
            printf '%s\n' "$*" >> "$DOTNET_TEST_LOG"
            if [[ "${1:-}" == test ]]; then
              while [[ $# -gt 0 ]]; do
                if [[ "$1" == --results-directory ]]; then
                  mkdir -p "$2"
                  cp "$DOTNET_TEST_FIXTURE_TRX" "$2/selected.trx"
                  exit 0
                fi
                shift
              done
              exit 2
            fi
            exec "$REAL_DOTNET" "$@"
            """);
        var dotnetPath = TestProcessRunner.Run("/bin/bash", ["-c", "command -v dotnet"],
            root, TestBudgets.ScriptProcessHangGuard, 4096);
        Assert.Equal(0, dotnetPath.ExitCode);
        var target = scope switch
        {
            "solution" => Path.Combine(root, "tools/StrataLint.sln"),
            "project" => Path.Combine(root, selectedProject),
            "relative-project" => selectedProject["tools/".Length..],
            "unknown" => Path.Combine(root, "tools/tests/Unregistered/Unregistered.csproj"),
            "outside" => Path.Combine(fixture.Path, "Outside.csproj"),
            "production" => Path.Combine(root, "tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj"),
            _ => throw new ArgumentException("unknown fixture scope", nameof(scope)),
        };
        var result = TestProcessRunner.Run("env",
            ["-u", "MAKEFLAGS", "-u", "MAKEOVERRIDES", "-u", "TEST_PROJECT", "-u", "TEST_FILTER",
                $"PATH={binDirectory}:/usr/bin:/bin", $"REAL_DOTNET={Encoding.UTF8.GetString(dotnetPath.StandardOutput).Trim()}",
                $"DOTNET_TEST_LOG={log}", $"DOTNET_TEST_FIXTURE_TRX={trx}",
                $"TEST_RESULTS_DIRECTORY={Path.Combine(fixture.Path, "results")}",
                "make", "--no-print-directory", "-C", "tools", "test", $"TEST_PROJECT={target}",
                $"TEST_FILTER={(filtered ? "FullyQualifiedName~Fixture" : "")}"],
            // This invokes the complete make -> dotnet-test -> TRX verification
            // workflow; the timeout is infrastructure-only and must cover the
            // workflow under the full parallel suite.
            root, TestBudgets.WorkflowProcessHangGuard, 64 * 1024);
        var output = Encoding.UTF8.GetString(result.StandardOutput);
        var error = Encoding.UTF8.GetString(result.StandardError);
        Assert.True(result.ExitCode == expectedExit, $"expected exit {expectedExit}, actual {result.ExitCode}\n{output}\n{error}");
        Assert.Single(File.ReadAllLines(log), line => line.StartsWith("test ", StringComparison.Ordinal));
        if (expectedExit == 0 && (!filtered || scope != "solution"))
        {
            var required = scope == "solution" ? owners : [selectedAssembly];
            foreach (var assembly in required)
                Assert.Contains($"TEST_ASSEMBLY_EVIDENCE_ACCEPTED assembly={assembly} evidence=trx executed=1", output, StringComparison.Ordinal);
            Assert.Equal(required.Length, output.Split('\n').Count(line => line.StartsWith("TEST_ASSEMBLY_EVIDENCE_ACCEPTED ", StringComparison.Ordinal)));
        }
        else if (scope is "unknown" or "outside" or "production")
        {
            Assert.Contains("ENGINEERING_TEST_PLAN_FAILED " + (scope == "outside"
                ? "test target is outside repository" : "test target is not a registered test project"), error, StringComparison.Ordinal);
        }
        else if (expectedExit != 0)
        {
            var failure = evidence == "zero" ? "dotnet test executed zero tests"
                : "TRX has no executed identity from required assembly " + (scope == "solution" ? otherAssembly : selectedAssembly);
            Assert.Contains("TEST_EVIDENCE_FAILED " + failure, error, StringComparison.Ordinal);
        }
    }

    [Fact(DisplayName = "dotnet-test rejects a zero-match filter on Bash 3.2")]
    public void DotnetTestRejectsZeroMatchFilterOnBash32()
    {
        if (OperatingSystem.IsWindows()) return;

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var binDirectory = Path.Combine(fixture.Path, "bin");
        var fakeDotnet = Path.Combine(binDirectory, "dotnet");
        var log = Path.Combine(fixture.Path, "dotnet.log");
        Directory.CreateDirectory(binDirectory);
        WriteExecutable(
            fakeDotnet,
            """
            #!/bin/bash
            printf '%s\n' "$*" >> "$DOTNET_TEST_LOG"
            if [[ "${1:-}" == test ]]; then
              results=""
              while [[ $# -gt 0 ]]; do
                if [[ "$1" == --results-directory ]]; then results="$2"; break; fi
                shift
              done
              mkdir -p "$results"
              printf '<TestRun><ResultSummary outcome="Completed"><Counters executed="%s" /></ResultSummary></TestRun>\n' "$TRX_EXECUTED" > "$results/fake.trx"
              exit 0
            fi
            if [[ "$*" == *"verify-trx"* ]]; then exec "$REAL_DOTNET" "$@"; fi
            exit 0
            """);

        var dotnetPath = TestProcessRunner.Run(
            "/bin/bash",
            ["-c", "command -v dotnet"],
            root,
            TestBudgets.ScriptProcessHangGuard,
            4096);
        Assert.Equal(0, dotnetPath.ExitCode);
        var realDotnet = Encoding.UTF8.GetString(dotnetPath.StandardOutput).Trim();
        var result = TestProcessRunner.Run(
            "env",
            [
                $"PATH={binDirectory}:/usr/bin:/bin",
                $"REAL_DOTNET={realDotnet}",
                $"TRX_EXECUTED=0",
                $"DOTNET_TEST_LOG={log}",
                $"TEST_RESULTS_DIRECTORY={Path.Combine(fixture.Path, "results")}",
                "/bin/bash",
                Path.Combine(root, "tools/scripts/dotnet-test.sh"),
                "--filter", "FullyQualifiedName=No.Such.Test",
            ],
            root,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);

        Assert.NotEqual(0, result.ExitCode);
        var invocations = File.ReadAllLines(log);
        Assert.Contains(invocations, line => line.StartsWith("test ", StringComparison.Ordinal));
        Assert.Contains(invocations, line => line.Contains("verify-trx", StringComparison.Ordinal));
        Assert.Contains(
            "TEST_EVIDENCE_FAILED dotnet test executed zero tests",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    [Fact(DisplayName = "dotnet-test safely verifies an empty owner-argument array")]
    public void DotnetTestSafelyVerifiesEmptyOwnerArgumentArray()
    {
        if (OperatingSystem.IsWindows()) return;

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var binDirectory = Path.Combine(fixture.Path, "bin");
        var fakeDotnet = Path.Combine(binDirectory, "dotnet");
        var log = Path.Combine(fixture.Path, "dotnet.log");
        Directory.CreateDirectory(binDirectory);
        WriteExecutable(
            fakeDotnet,
            """
            #!/bin/bash
            printf '%s\n' "$*" >> "$DOTNET_TEST_LOG"
            if [[ "${1:-}" == test ]]; then
              results=""
              while [[ $# -gt 0 ]]; do
                if [[ "$1" == --results-directory ]]; then results="$2"; break; fi
                shift
              done
              mkdir -p "$results"
              printf '<TestRun><Results><UnitTestResult testId="one" testName="Fixture.Runs" outcome="Passed" /></Results><TestDefinitions><UnitTest id="one" storage="Fixture.dll"><TestMethod className="Fixture" name="Runs" /></UnitTest></TestDefinitions><ResultSummary outcome="Completed"><Counters executed="1" passed="1" /></ResultSummary></TestRun>\n' > "$results/fake.trx"
              exit 0
            fi
            if [[ "$*" == *"verify-trx"* ]]; then exec "$REAL_DOTNET" "$@"; fi
            exit 0
            """);

        var dotnetPath = TestProcessRunner.Run(
            "/bin/bash",
            ["-c", "command -v dotnet"],
            root,
            TestBudgets.ScriptProcessHangGuard,
            4096);
        Assert.Equal(0, dotnetPath.ExitCode);
        var realDotnet = Encoding.UTF8.GetString(dotnetPath.StandardOutput).Trim();
        var result = TestProcessRunner.Run(
            "env",
            [
                $"PATH={binDirectory}:/usr/bin:/bin",
                $"REAL_DOTNET={realDotnet}",
                $"DOTNET_TEST_LOG={log}",
                $"TEST_RESULTS_DIRECTORY={Path.Combine(fixture.Path, "results")}",
                "/bin/bash",
                Path.Combine(root, "tools/scripts/dotnet-test.sh"),
                "--filter", "FullyQualifiedName=Existing.Test",
            ],
            root,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);

        Assert.Equal(0, result.ExitCode);
        Assert.Contains(
            "TEST_EVIDENCE_ACCEPTED evidence=trx executed=1",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
        Assert.Contains(
            File.ReadAllLines(log),
            line => line.Contains("verify-trx", StringComparison.Ordinal));
    }

}
