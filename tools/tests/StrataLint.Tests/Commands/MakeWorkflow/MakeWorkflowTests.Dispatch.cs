using System.Text.RegularExpressions;
using System.Text;
using System.Text.Json;
using System.Xml.Linq;
using StrataLint.Engine;
using YamlDotNet.RepresentationModel;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{

    [Fact(DisplayName = "Makefile remains a thin complete dispatch table")]
    public void MakefileIsAThinCompleteDispatchTable()
    {
        var root = TestRepositoryLayout.FindRoot();
        var makefile = File.ReadAllText(Path.Combine(root, "Makefile"));

        Assert.Contains(".DEFAULT_GOAL := help", makefile, StringComparison.Ordinal);
        var phony = Assert.Single(
            makefile.Split('\n'),
            static line => line.StartsWith(".PHONY:", StringComparison.Ordinal));
        Assert.Equal(RootTargets, phony[".PHONY:".Length..].Split(' ', StringSplitOptions.RemoveEmptyEntries));
        foreach (var target in RootTargets)
        {
            Assert.Matches(new Regex($"(?m)^{Regex.Escape(target)}:", RegexOptions.CultureInvariant), makefile);
            Assert.InRange(RecipeCount(makefile, target), 0, 1);
        }

        Assert.Contains("build: lean", makefile, StringComparison.Ordinal);
        Assert.Equal(0, RecipeCount(makefile, "build"));
        // `scribe-strip` retired with the Scribe receipt field it existed to remove; the
        // target must be gone from both the recipe list and the help text.
        Assert.DoesNotContain("scribe-strip", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("strip-scribe-receipts", makefile, StringComparison.Ordinal);
        // make test 是薄委托;数学门链条的唯一真源在 math-gate.sh 里,断言脚本本体。
        var mathematicalTestRecipe = Recipe(makefile, "test");
        Assert.DoesNotContain("dotnet test", mathematicalTestRecipe, StringComparison.Ordinal);
        Assert.Contains("tools/scripts/workflow/math-gate.sh", mathematicalTestRecipe, StringComparison.Ordinal);
        Assert.Equal(
            $"\t@/bin/bash {LeanCacheEnsureScriptPath}",
            Recipe(makefile, "lean-cache-ensure"));
        Assert.Equal(
            $"\t@/bin/bash {WarmDonorScriptPath}",
            Recipe(makefile, "warm-donor"));
        var warmDonor = File.ReadAllText(Path.Combine(root, WarmDonorScriptPath));
        Assert.Contains("git pull --ff-only origin dev", warmDonor, StringComparison.Ordinal);
        Assert.Contains("make -C \"$ROOT\" lean", warmDonor, StringComparison.Ordinal);
        Assert.DoesNotContain("lsof", warmDonor, StringComparison.Ordinal);
        Assert.DoesNotContain("LeanCacheBusyProbe", warmDonor, StringComparison.Ordinal);
        foreach (var excludedCaller in new[]
        {
            WorktreeInitScriptPath,
            LeanCacheEnsureScriptPath,
            PreflightScriptPath,
            "tools/scripts/workflow/math-gate.sh",
            LocalHarnessGateScriptPath,
        })
        {
            var excludedText = File.ReadAllText(Path.Combine(root, excludedCaller));
            Assert.DoesNotContain(
                WarmDonorScriptPath,
                excludedText,
                StringComparison.Ordinal);
            Assert.DoesNotContain(
                "warm-donor",
                excludedText,
                StringComparison.Ordinal);
        }
        var leanRecipe = Recipe(makefile, "lean");
        Assert.Contains(LeanCacheRunScriptPath, leanRecipe, StringComparison.Ordinal);
        Assert.Contains("lake build", leanRecipe, StringComparison.Ordinal);
        Assert.Contains(LeanReportScriptPath, Recipe(makefile, "lean-report"), StringComparison.Ordinal);
        var inspector = File.ReadAllText(Path.Combine(root, "tools", "lean-inspector", "inspect.sh"));
        Assert.DoesNotContain("run_phase cache-get", inspector, StringComparison.Ordinal);
        Assert.DoesNotContain("run_phase report \"$LAKE\"", inspector, StringComparison.Ordinal);
        Assert.Contains(LeanCacheRunScriptPath, inspector, StringComparison.Ordinal);
        Assert.Contains(
            $"run_phase report \"$REPOSITORY/{LeanCacheRunScriptPath}\" \"$LAKE\" build :report",
            inspector,
            StringComparison.Ordinal);

        int EnsureDependency(string target)
        {
            var header = Assert.Single(
                makefile.Split('\n'),
                line => line.StartsWith(target + ":", StringComparison.Ordinal));
            return header[(target.Length + 1)..]
                .Split(' ', StringSplitOptions.RemoveEmptyEntries)
                .Count(static prerequisite => prerequisite == "lean-cache-ensure");
        }

        var leanCommands = Regex.Matches(
            Recipe(makefile, "lean"),
            Regex.Escape(LeanCacheRunScriptPath),
            RegexOptions.CultureInvariant).Count;
        var leanEnsures = EnsureDependency("lean") + leanCommands;
        var buildEnsures = EnsureDependency("build") + leanEnsures;

        Assert.Equal(1, leanCommands);
        Assert.Equal(1, leanEnsures);
        Assert.Equal(1, buildEnsures);
        var cacheEnsure = File.ReadAllText(Path.Combine(root, LeanCacheEnsureScriptPath));
        Assert.DoesNotContain("[[ -L", cacheEnsure, StringComparison.Ordinal);
        Assert.DoesNotContain("[[ -d", cacheEnsure, StringComparison.Ordinal);
        Assert.Contains(ScribeScriptPath + " emit", Recipe(makefile, "emit"), StringComparison.Ordinal);
        Assert.Contains(IngestScriptPath, Recipe(makefile, "ingest"), StringComparison.Ordinal);
        Assert.Contains(
            IngestScriptPath + " align-digestion-status",
            Recipe(makefile, "align-digestion-status"),
            StringComparison.Ordinal);
        Assert.Equal(
            $"\t@/bin/bash {IngestScriptPath} mathlib-reanchor \"$(BASE)\"",
            Recipe(makefile, "mathlib-reanchor"));
        // The four targets that reach the command line keep the verb in the Makefile and stay one
        // recipe line: the dispatch table above allows at most one line per target, and
        // CliVerbLinkageTests reads the verb out of this file to prove it is registered. The same
        // line first checks that the build output exists and builds it when it does not, because a
        // fresh worktree carries none; on 2026-09-11 two of five implementation seats hit a raw
        // process-start exception six times between them while every brief opens by calling show-atom.
        foreach (var noBuildTarget in new[] { "show-atom", "atom-context", "settle", "settle-clear" })
        {
            var recipe = Recipe(makefile, noBuildTarget);
            Assert.Contains("dotnet run --no-build --project", recipe, StringComparison.Ordinal);
            Assert.Contains(
                "@test -x tools/StrataLint.Cli/bin/Release/net10.0/StrataLint || dotnet build",
                recipe,
                StringComparison.Ordinal);
        }
        Assert.Contains(
            EchoResidualSummaryScriptPath,
            Recipe(makefile, "echo-residual-summary"),
            StringComparison.Ordinal);
        Assert.Contains(LocalHarnessGateScriptPath, Recipe(makefile, "gate"), StringComparison.Ordinal);
        Assert.Equal(
            $"\t@MODE=\"$(MODE)\" BASE=\"$(BASE)\" /bin/bash {PreflightScriptPath}",
            Recipe(makefile, "preflight"));
        var worktreeRecipe = Recipe(makefile, "worktree");
        Assert.Contains(WorktreeInitScriptPath, worktreeRecipe, StringComparison.Ordinal);
        Assert.Contains("\"$(KIND)\" \"$(NAME)\"", worktreeRecipe, StringComparison.Ordinal);
        Assert.Contains("\"$(WORKTREE_DEST)\"", worktreeRecipe, StringComparison.Ordinal);
        // 回收**不得**是建树的前置(#2769)。此前它是依赖形式,于是每次 `make worktree`
        // 都无条件回收所有「已合并且干净」的 lane —— 而那正是一条刚建好、worker 尚未落笔
        // 的 lane 的默认状态。实测后果:另一会话建树时删掉了本会话正在使用的 lane、其分支
        // 与约 15G 热缓存,一条实施席因此 blocked。
        //
        // 原断言的注释里已写明「判官树的判据区分不了『跑完了』和『正在跑』」,并以
        // `--lanes-only` 缓解;但那限定的是「哪些东西算 lane」,**不是「谁的 lane」**,
        // 对跨会话误删不构成防护。
        //
        // 反转而非删除:删掉断言就没有东西拦住同一个直觉(「开工前先扫干净」)把依赖加回来。
        Assert.DoesNotContain("worktree: worktree-clean", makefile, StringComparison.Ordinal);
        // `worktree-clean` 保留为**显式**目标:回收本身没错,错的是让建树隐含回收。
        var worktreeCleanRecipe = Recipe(makefile, "worktree-clean");
        Assert.Contains(CleanLanesScriptPath, worktreeCleanRecipe, StringComparison.Ordinal);
        Assert.Contains("--lanes-only", worktreeCleanRecipe, StringComparison.Ordinal);
        Assert.Contains("--force", worktreeCleanRecipe, StringComparison.Ordinal);
        Assert.Contains("WORKTREE_DEST = $(if $(DEST)", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("$(origin PATH)", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("$(PATH)", makefile, StringComparison.Ordinal);
        Assert.Contains("[DEST=DIR]", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("[PATH=DIR]", makefile, StringComparison.Ordinal);
        Assert.Contains(PrOpenScriptPath, Recipe(makefile, "pr-open"), StringComparison.Ordinal);
        Assert.Contains("--head \"$(HEAD)\"", Recipe(makefile, "pr-open"), StringComparison.Ordinal);
        Assert.DoesNotContain("pr-update", makefile, StringComparison.Ordinal);
        foreach (var removed in ToolsTargets.Except(["help", "test"], StringComparer.Ordinal))
        {
            Assert.DoesNotContain($"\n{removed}:", "\n" + makefile, StringComparison.Ordinal);
        }
        Assert.DoesNotContain("\ntools-test:", "\n" + makefile, StringComparison.Ordinal);
    }

    [Fact]
    public void RootMakefileExposesOnlyThinPrOpenAndPrWatchDispatch()
    {
        var makefile = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), "Makefile"));
        var openRecipe = Recipe(makefile, "pr-open");
        var watchRecipe = Recipe(makefile, "pr-watch");

        Assert.Contains("make pr-open HEAD=branch MESSAGE=file [AUTO_MERGE=1]  Create from a message file, optionally arm auto-merge, and wait for required-CI verdict", makefile, StringComparison.Ordinal);
        Assert.Contains("make pr-watch PR=n                Wait for required-CI verdict on an existing PR", makefile, StringComparison.Ordinal);
        Assert.Single(Regex.Matches(openRecipe, Regex.Escape(PrOpenScriptPath)));
        Assert.Single(Regex.Matches(watchRecipe, Regex.Escape(PrWatchScriptPath)));
        Assert.Contains("$(if $(filter 1,$(AUTO_MERGE)),--auto-merge,)", openRecipe, StringComparison.Ordinal);
        Assert.Contains("--timeout-seconds \"$(WATCH_TIMEOUT_SECONDS)\"", openRecipe, StringComparison.Ordinal);
        Assert.Contains("--interval-seconds \"$(WATCH_INTERVAL_SECONDS)\"", openRecipe, StringComparison.Ordinal);
        Assert.Contains("--pr \"$(PR)\"", watchRecipe, StringComparison.Ordinal);
        Assert.Contains("--timeout-seconds \"$(WATCH_TIMEOUT_SECONDS)\"", watchRecipe, StringComparison.Ordinal);
        Assert.Contains("--interval-seconds \"$(WATCH_INTERVAL_SECONDS)\"", watchRecipe, StringComparison.Ordinal);
        foreach (var recipe in new[] { openRecipe, watchRecipe })
        {
            Assert.DoesNotContain("gh ", recipe, StringComparison.Ordinal);
            Assert.DoesNotContain("while", recipe, StringComparison.Ordinal);
            Assert.DoesNotContain("sleep", recipe, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void CheckFastFilterIsNonEmptyAndPinsRequiredRepositoryChecks()
    {
        var makefile = File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools", "Makefile"));
        var filterLine = Assert.Single(
            makefile.Split('\n'),
            static line => line.StartsWith(CheckFastFilterVariable, StringComparison.Ordinal));
        var filter = filterLine[CheckFastFilterVariable.Length..].Trim();

        Assert.False(string.IsNullOrWhiteSpace(filter));
        Assert.Equal(
            [
                "FullyQualifiedName~StrataLint.Tests.CapacityAuditCommandTests",
                "FullyQualifiedName~StrataLint.ArchitectureTests.RepositoryIoAccessPolicyTests",
                "FullyQualifiedName~StrataLint.ArchitectureTests.BannedApiCoverageTests",
                "FullyQualifiedName=StrataLint.Tests.MakeWorkflowTests.CheckFastFilterIsNonEmptyAndPinsRequiredRepositoryChecks",
            ],
            filter.Split('|', StringSplitOptions.RemoveEmptyEntries));
    }

    [Fact]
    public void ToolsMakefileIsAThinCompleteDispatchTable()
    {
        var root = TestRepositoryLayout.FindRoot();
        var makefile = File.ReadAllText(Path.Combine(root, ToolsMakefilePath));

        Assert.Contains(".DEFAULT_GOAL := help", makefile, StringComparison.Ordinal);
        Assert.Contains(
            "HERE := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))",
            makefile,
            StringComparison.Ordinal);
        var phony = Assert.Single(
            makefile.Split('\n'),
            static line => line.StartsWith(".PHONY:", StringComparison.Ordinal));
        Assert.Equal(ToolsTargets.Order(StringComparer.Ordinal),
            phony[".PHONY:".Length..].Split(' ', StringSplitOptions.RemoveEmptyEntries).Order(StringComparer.Ordinal));
        foreach (var target in ToolsTargets)
        {
            Assert.Matches(new Regex($"(?m)^{Regex.Escape(target)}:", RegexOptions.CultureInvariant), makefile);
            Assert.InRange(RecipeCount(makefile, target), 0, 1);
        }

        Assert.Contains("$(HERE)/scripts/dotnet-build.sh", Recipe(makefile, "dotnet"), StringComparison.Ordinal);
        Assert.Equal(
            "\t@PYTHONDONTWRITEBYTECODE=1 PYTORCH_ENABLE_MPS_FALLBACK=0 uv run --python 3.12 --with torch==2.8.0 --with numpy==2.0.2 --with python-flint==0.8.0 python \"$(HERE)/scripts/agent/xi_quantization.py\" " +
            "--mode \"$(XI_MODE)\" --first \"$(XI_FIRST)\" --last \"$(XI_LAST)\" --chunk \"$(XI_CHUNK)\" --precision \"$(XI_PRECISION)\" --digits \"$(XI_DIGITS)\" --state-dir \"$(XI_STATE)\" --report \"$(XI_REPORT)\"",
            Recipe(makefile, "xi-quantization"));
        Assert.Equal(
            "\t@python3 -B \"$(HERE)/scripts/agent/test_xi_quantization.py\"",
            Recipe(makefile, "xi-quantization-test"));
        foreach (var script in new[] { "xi_quantization.py", "test_xi_quantization.py" })
        {
            Assert.True(File.Exists(Path.Combine(root, "tools", "scripts", "agent", script)));
        }
        var helpRecipe = Recipe(makefile, "help");
        Assert.Contains("make -C tools xi-quantization [", helpRecipe, StringComparison.Ordinal);
        Assert.Contains("make -C tools xi-quantization-test ", helpRecipe, StringComparison.Ordinal);
        var testRecipe = Recipe(makefile, "test");
        Assert.Contains("TEST_PROJECT ?= $(HERE)/StrataLint.sln", makefile, StringComparison.Ordinal);
        Assert.Contains("scripts/dotnet-test.sh \"$(TEST_PROJECT)\"", testRecipe, StringComparison.Ordinal);
        Assert.Contains("$(if $(TEST_FILTER),--filter \"$(TEST_FILTER)\",)", testRecipe, StringComparison.Ordinal);
        foreach (var selected in OperatingSystem.IsWindows() ? Array.Empty<bool>() : new[] { false, true })
        {
            const string project = "selected tests/Probe.csproj";
            const string filter = "FullyQualifiedName=Probe.First|FullyQualifiedName=Probe.Second";
            var dispatch = TestProcessRunner.Run("/usr/bin/env",
                ["-u", "MAKEFLAGS", "-u", "MAKEOVERRIDES", "-u", "TEST_PROJECT", "-u", "TEST_FILTER",
                    "make", "--no-print-directory", "-n", "-C", "tools", "test", .. selected
                    ? new[] { $"TEST_PROJECT={project}", $"TEST_FILTER={filter}" }
                    : new[] { "TEST_FILTER=" }],
                root, TestBudgets.ScriptProcessHangGuard, 64 * 1024);
            Assert.True(dispatch.ExitCode == 0, Encoding.UTF8.GetString(dispatch.StandardError));
            var expected = $"/bin/bash {root}/tools/scripts/dotnet-test.sh \"{(selected ? project : root + "/tools/StrataLint.sln")}\""
                + (selected ? $" --filter \"{filter}\"" : "");
            Assert.Equal(expected, Encoding.UTF8.GetString(dispatch.StandardOutput).Trim());
        }
        var dotnetTest = File.ReadAllText(Path.Combine(root, "tools", "scripts", "dotnet-test.sh"));
        Assert.Contains("dotnet test \"$@\"", dotnetTest, StringComparison.Ordinal);
        Assert.Contains(
            "list-test-owner-assemblies --repository \"$ROOT\"",
            dotnetTest,
            StringComparison.Ordinal);
        Assert.Contains(
            "OWNER_ASSEMBLY_ARGS+=(--required-assembly \"$owner_assembly\")",
            dotnetTest,
            StringComparison.Ordinal);
        Assert.Contains(
            "verify-trx --results-directory \"$RESULTS_DIRECTORY\"",
            dotnetTest,
            StringComparison.Ordinal);
        Assert.Contains(
            "${OWNER_ASSEMBLY_ARGS[@]+\"${OWNER_ASSEMBLY_ARGS[@]}\"}",
            dotnetTest,
            StringComparison.Ordinal);
        Assert.Contains("$(HERE)/scripts/stratalint-selftest.sh", Recipe(makefile, "selftest"), StringComparison.Ordinal);
        Assert.Contains(
            "$(HERE)/scripts/update-renderer-contract.sh",
            Recipe(makefile, "update-renderer-contract"),
            StringComparison.Ordinal);

        // The recipe assertion above only checks the Makefile text. A recipe naming a script
        // that does not exist is a dangling reference, so the entrypoint itself is checked here.
        Assert.True(
            File.Exists(Path.Combine(root, RendererContractUpdateScriptPath)),
            $"{RendererContractUpdateScriptPath} is named by the update-renderer-contract recipe but is absent");
        Assert.Contains("$(HERE)/scripts/clean-lanes.sh", Recipe(makefile, "clean-lanes"), StringComparison.Ordinal);
        Assert.DoesNotContain("refactor-p0-0-gate-authority", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("--old-build", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("OUT ?=", makefile, StringComparison.Ordinal);
    }

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

    [Fact(DisplayName = "dotnet-test rejects a root discovery failure with stdout on Bash 3.2")]
    public void DotnetTestRejectsRootDiscoveryFailureWithStdoutOnBash32()
    {
        if (OperatingSystem.IsWindows()) return;

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var binDirectory = Path.Combine(fixture.Path, "bin");
        var fakeDirname = Path.Combine(binDirectory, "dirname");
        var fakeDotnet = Path.Combine(binDirectory, "dotnet");
        var invocationMarker = Path.Combine(fixture.Path, "dotnet-invoked");
        Directory.CreateDirectory(binDirectory);
        WriteExecutable(
            fakeDirname,
            """
            #!/bin/bash
            printf '%s\n' "$DOTNET_TEST_SCRIPT_DIRECTORY"
            exit 7
            """);
        WriteExecutable(
            fakeDotnet,
            """
            #!/bin/bash
            printf 'invoked\n' > "$DOTNET_TEST_INVOCATION_MARKER"
            if [[ "${1:-}" == test ]]; then
              results=""
              while [[ $# -gt 0 ]]; do
                if [[ "$1" == --results-directory ]]; then results="$2"; break; fi
                shift
              done
              mkdir -p "$results"
              printf '<TestRun><Results><UnitTestResult testId="one" testName="Fixture.Runs" outcome="Passed" /></Results><TestDefinitions><UnitTest id="one" storage="Fixture.dll"><TestMethod className="Fixture" name="Runs" /></UnitTest></TestDefinitions><ResultSummary outcome="Completed"><Counters executed="1" passed="1" /></ResultSummary></TestRun>\n' > "$results/fake.trx"
            fi
            exit 0
            """);

        var result = TestProcessRunner.Run(
            "env",
            [
                $"PATH={binDirectory}:/usr/bin:/bin",
                $"DOTNET_TEST_SCRIPT_DIRECTORY={Path.Combine(root, "tools", "scripts")}",
                $"DOTNET_TEST_INVOCATION_MARKER={invocationMarker}",
                $"TEST_RESULTS_DIRECTORY={Path.Combine(fixture.Path, "results")}",
                "/bin/bash",
                Path.Combine(root, "tools/scripts/dotnet-test.sh"),
                "--filter", "FullyQualifiedName=Root.Discovery.Probe",
            ],
            root,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);

        Assert.NotEqual(0, result.ExitCode);
        Assert.False(
            File.Exists(invocationMarker),
            "root discovery must fail before dotnet executes");
    }

    [Fact(DisplayName = "dotnet-test rejects EXIT zero before its completion marker")]
    public void DotnetTestRejectsExitZeroBeforeCompletionMarker()
    {
        if (OperatingSystem.IsWindows()) return;

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var binDirectory = Path.Combine(fixture.Path, "bin");
        var fakeDotnet = Path.Combine(binDirectory, "dotnet");
        var bashEnvironment = Path.Combine(fixture.Path, "exit-before-completion.sh");
        var invocationMarker = Path.Combine(fixture.Path, "dotnet-invoked");
        Directory.CreateDirectory(binDirectory);
        WriteExecutable(
            fakeDotnet,
            """
            #!/bin/bash
            printf 'invoked\n' > "$DOTNET_TEST_INVOCATION_MARKER"
            exit 0
            """);
        File.WriteAllText(
            bashEnvironment,
            """
            trap 'case "$BASH_COMMAND" in dotnet\ test*) trap - DEBUG; exit 0 ;; esac' DEBUG
            """);

        var result = TestProcessRunner.Run(
            "env",
            [
                $"PATH={binDirectory}:/usr/bin:/bin",
                $"BASH_ENV={bashEnvironment}",
                $"DOTNET_TEST_INVOCATION_MARKER={invocationMarker}",
                $"TEST_RESULTS_DIRECTORY={Path.Combine(fixture.Path, "results")}",
                "/bin/bash",
                Path.Combine(root, "tools/scripts/dotnet-test.sh"),
                "--filter", "FullyQualifiedName=Completion.Probe",
            ],
            root,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);

        Assert.False(
            File.Exists(invocationMarker),
            "the completion probe must exit before dotnet executes");
        Assert.NotEqual(0, result.ExitCode);
    }

    [Fact]
    public void HelpRunsAndNamesEveryTarget()
    {
        var root = TestRepositoryLayout.FindRoot();
        var rootResult = TestProcessRunner.Run(
            "make",
            ["help"],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        var toolsResult = TestProcessRunner.Run(
            "make",
            ["-C", "tools", "help"],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);
        var directToolsResult = TestProcessRunner.Run(
            "make",
            ["-f", "tools/Makefile", "help"],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        Assert.Equal(0, rootResult.ExitCode);
        var rootOutput = System.Text.Encoding.UTF8.GetString(rootResult.StandardOutput);
        Assert.All(RootTargets, target => Assert.Contains($"make {target}", rootOutput, StringComparison.Ordinal));
        Assert.Contains("values", rootOutput, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain("make dotnet", rootOutput, StringComparison.Ordinal);
        Assert.DoesNotContain("make tools-test", rootOutput, StringComparison.Ordinal);
        Assert.DoesNotContain("pr-update", rootOutput, StringComparison.Ordinal);

        Assert.Equal(0, toolsResult.ExitCode);
        var toolsOutput = System.Text.Encoding.UTF8.GetString(toolsResult.StandardOutput);
        Assert.All(
            ToolsTargets,
            target => Assert.Contains($"make -C tools {target}", toolsOutput, StringComparison.Ordinal));
        Assert.Contains("dry-run", toolsOutput, StringComparison.Ordinal);
        Assert.Contains("FORCE=1", toolsOutput, StringComparison.Ordinal);
        Assert.DoesNotContain("make -C tools lean", toolsOutput, StringComparison.Ordinal);
        Assert.Equal(0, directToolsResult.ExitCode);
        var directToolsOutput = System.Text.Encoding.UTF8.GetString(directToolsResult.StandardOutput);
        Assert.All(
            ToolsTargets,
            target => Assert.Contains($"make -C tools {target}", directToolsOutput, StringComparison.Ordinal));
    }
}
