using System.Text.RegularExpressions;
using System.Text;
using StrataLint.EngineeringScope;
using StrataLint.Engine;
using YamlDotNet.RepresentationModel;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{

    [Fact(DisplayName = "Makefile and inspector dispatch counts are pinned in the thin dispatch table")]
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
        // make test 是薄委托;数学门链条的唯一真源在 math-gate.sh 里,断言脚本本体。
        var mathematicalTestRecipe = Recipe(makefile, "test");
        Assert.DoesNotContain("dotnet test", mathematicalTestRecipe, StringComparison.Ordinal);
        Assert.Contains("tools/scripts/workflow/math-gate.sh", mathematicalTestRecipe, StringComparison.Ordinal);
        var mathGate = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), "tools", "scripts", "workflow", "math-gate.sh"));
        Assert.DoesNotContain("dotnet test", mathGate, StringComparison.Ordinal);
        Assert.Contains("/../../..\" && pwd -P)", mathGate, StringComparison.Ordinal);
        Assert.Contains("make lean", mathGate, StringComparison.Ordinal);
        Assert.DoesNotContain("lake build", mathGate, StringComparison.Ordinal);
        Assert.Contains("make lean-report", mathGate, StringComparison.Ordinal);
        // check 在干净树须锚定 merge-base(候选不能自我保护)且容忍 rc=3 预期路径。
        Assert.Contains(" check \"${CHECK_BASE_ARGS[@]}\" --candidate-lean-report ", mathGate, StringComparison.Ordinal);
        Assert.Contains("--protected-base \"$base_sha\"", mathGate, StringComparison.Ordinal);
        Assert.Contains("[ \"$check_rc\" -ne 0 ] && [ \"$check_rc\" -ne 3 ]", mathGate, StringComparison.Ordinal);
        Assert.Contains(ScribeContentChecksScriptPath, mathGate, StringComparison.Ordinal);
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
        Assert.DoesNotContain("run_phase build \"$LAKE\"", inspector, StringComparison.Ordinal);
        Assert.Contains(LeanCacheRunScriptPath, inspector, StringComparison.Ordinal);
        Assert.Contains("run_phase build \"$CACHE_RUN\" \"$LAKE\" build", inspector, StringComparison.Ordinal);
        Assert.Contains("\"$CACHE_RUN\" \"$LAKE\" env lean", inspector, StringComparison.Ordinal);

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
        var reportCommands = Regex.Matches(
            inspector,
            "(?m)^(?!\\[\\[).*\\\"\\$CACHE_RUN\\\"",
            RegexOptions.CultureInvariant).Count;
        // lean-report needs both wrapper calls: inspect.sh:107 builds and inspect.sh:130 inspects.
        var leanEnsures = EnsureDependency("lean") + leanCommands;
        var reportEnsures = EnsureDependency("lean-report") + reportCommands;
        var testEnsures = EnsureDependency("test") + leanEnsures + reportEnsures;
        var buildEnsures = EnsureDependency("build") + leanEnsures;

        Assert.Equal(1, leanCommands);
        Assert.Equal(2, reportCommands);
        Assert.Equal(1, leanEnsures);
        Assert.Equal(2, reportEnsures);
        Assert.Equal(3, testEnsures);
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
        var showAtomRecipe = Recipe(makefile, "show-atom");
        Assert.Contains("dotnet run --no-build --project", showAtomRecipe, StringComparison.Ordinal);
        Assert.Contains(" show-atom --atom-id \"$(ATOM_ID)\"", showAtomRecipe, StringComparison.Ordinal);
        Assert.Contains(
            EchoResidualSummaryScriptPath,
            Recipe(makefile, "echo-residual-summary"),
            StringComparison.Ordinal);
        Assert.Contains(LocalHarnessGateScriptPath, Recipe(makefile, "gate"), StringComparison.Ordinal);
        Assert.Equal(
            $"\t@BASE=\"$(BASE)\" /bin/bash {PreflightScriptPath}",
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
                "FullyQualifiedName=StrataLint.ArchitectureTests.CapacityPolicyTests.RepositoryHasNoOversizeArtifactOrOverfullDirectory",
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
        Assert.Equal(ToolsTargets, phony[".PHONY:".Length..].Split(' ', StringSplitOptions.RemoveEmptyEntries));
        foreach (var target in ToolsTargets)
        {
            Assert.Matches(new Regex($"(?m)^{Regex.Escape(target)}:", RegexOptions.CultureInvariant), makefile);
            Assert.InRange(RecipeCount(makefile, target), 0, 1);
        }

        Assert.Contains("$(HERE)/scripts/dotnet-build.sh", Recipe(makefile, "dotnet"), StringComparison.Ordinal);
        var testRecipe = Recipe(makefile, "test");
        Assert.Contains("scripts/dotnet-test.sh $(HERE)/StrataLint.sln", testRecipe, StringComparison.Ordinal);
        Assert.DoesNotContain("--filter", testRecipe, StringComparison.Ordinal);
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
        var engineeringTestsRecipe = Recipe(makefile, "engineering-tests");
        Assert.Contains(
            "StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj",
            engineeringTestsRecipe,
            StringComparison.Ordinal);
        Assert.Contains("REPOSITORY ?= $(HERE)/..", makefile, StringComparison.Ordinal);
        Assert.Contains("--repository \"$(REPOSITORY)\"", engineeringTestsRecipe, StringComparison.Ordinal);
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
              printf '<TestRun><ResultSummary><Counters executed="%s" /></ResultSummary></TestRun>\n' "$TRX_EXECUTED" > "$results/fake.trx"
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
              printf '<TestRun><ResultSummary><Counters executed="1" /></ResultSummary></TestRun>\n' > "$results/fake.trx"
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
              printf '<TestRun><ResultSummary><Counters executed="1" /></ResultSummary></TestRun>\n' > "$results/fake.trx"
            fi
            exit 0
            """);

        var result = TestProcessRunner.Run(
            "env",
            [
                $"PATH={binDirectory}:/usr/bin:/bin",
                $"DOTNET_TEST_SCRIPT_DIRECTORY={Path.Combine(root, "tools", "scripts")}",
                $"DOTNET_TEST_INVOCATION_MARKER={invocationMarker}",
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

    [Fact(DisplayName = "owner CLI output exactly matches the derived repository topology")]
    public void OwnerCliOutputExactlyMatchesDerivedRepositoryTopology()
    {
        var root = TestRepositoryLayout.FindRoot();
        var snapshot = RepositoryRules.ReadTrackedProjects(root);
        var expected = RepositoryRules.CalculateOwnerAssemblies(snapshot).ToArray();
        using var output = new StringWriter { NewLine = "\n" };
        using var error = new StringWriter { NewLine = "\n" };
        var result = Program.Run(
            ["list-test-owner-assemblies", "--repository", root],
            static _ => throw new InvalidOperationException("evidence loader is not used"),
            output,
            error);

        Assert.Equal(0, result);
        Assert.Empty(error.ToString());
        var actual = output.ToString()
            .Split('\n', StringSplitOptions.RemoveEmptyEntries);
        Assert.Equal(expected, actual);
        Assert.True(actual.Length >= 3, "the repository must have at least three owner assemblies");
    }

    [Fact(DisplayName = "owner CLI rejects a repository with zero derived owners")]
    public void OwnerCliRejectsZeroDerivedOwners()
    {
        using var fixture = new TemporaryDirectory();
        File.WriteAllText(Path.Combine(fixture.Path, "README.md"), "empty topology\n", Encoding.UTF8);
        ReviewRegressionTests.RunGit(fixture.Path, "init", "--quiet");
        ReviewRegressionTests.RunGit(fixture.Path, "add", ".");
        ReviewRegressionTests.RunGit(
            fixture.Path,
            "-c", "user.name=StrataLint Tests",
            "-c", "user.email=stratalint@example.invalid",
            "commit", "--quiet", "-m", "empty topology");

        using var output = new StringWriter { NewLine = "\n" };
        using var error = new StringWriter { NewLine = "\n" };
        var result = Program.Run(
            ["list-test-owner-assemblies", "--repository", fixture.Path],
            static _ => throw new InvalidOperationException("evidence loader is not used"),
            output,
            error);

        Assert.NotEqual(0, result);
        Assert.Contains(
            "derived zero owner assemblies",
            error.ToString(),
            StringComparison.Ordinal);
    }

    private static void AssertNoUnrecognizedGateCommands(string shell, string source)
    {
        foreach (var rawLine in shell.Split('\n'))
        {
            var line = rawLine.TrimEnd('\r');
            if (!Regex.IsMatch(
                    line,
                    """(?:dotnet[ \t]+"\$scribe"|run_scribe)[ \t]+\S+|make[ \t]+-C[ \t]+\S*tools[ \t]+\S+""",
                    RegexOptions.CultureInvariant | RegexOptions.NonBacktracking))
            {
                continue;
            }

            Assert.True(
                GateCommandSignatures(line).Any(),
                $"{source} contains an unrecognized gate command: '{line.Trim()}'.");
        }
    }

    private static IEnumerable<string> GateCommandSignatures(string shell)
    {
        foreach (Match match in Regex.Matches(
            shell,
            @"(?m)^[ \t]*(?:FULL=1[ \t]+)?(?:CI=true[ \t]+)?(?:STRATALINT_REQUIRE_LIVE_REPORT=1[ \t]+)?make[ \t]+-C[ \t]+(?:candidate/)?tools[ \t]+engineering-tests[ \t]+MODE=(?<mode>plan|execute)\b[^\r\n]*$",
            RegexOptions.CultureInvariant | RegexOptions.NonBacktracking))
        {
            yield return $"make -C tools engineering-tests MODE={match.Groups["mode"].Value}";
        }

        foreach (Match match in Regex.Matches(
            shell,
            @"(?m)^[ \t]*(?:CI=true[ \t]+)?(?:STRATALINT_REQUIRE_LIVE_REPORT=1[ \t]+)?make[ \t]+-C[ \t]+(?:candidate/)?tools[ \t]+(?<target>dotnet|test|selftest)[ \t]*$",
            RegexOptions.CultureInvariant | RegexOptions.NonBacktracking))
        {
            yield return $"make -C tools {match.Groups["target"].Value}";
        }

        foreach (Match match in Regex.Matches(
            shell,
            """(?m)^[ \t]*(?:(?:STRATALINT_LEAN_REPORT="\$report"[ \t]+)?dotnet[ \t]+"\$scribe"|run_scribe)[ \t]+(?<arguments>(?:projections|emit|emit-values|describe-report|markdown-check)[^\r\n]*)$""",
            RegexOptions.CultureInvariant | RegexOptions.NonBacktracking))
        {
            yield return Regex.Replace(
                match.Groups["arguments"].Value.Trim(),
                @"\$(?:report|REPORT|EFFECTIVE_REPORT)",
                "$REPORT",
                RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);
        }

        var assignments = Regex.Matches(
                shell,
                """(?m)^[ \t]*(?<variable>[A-Za-z_][A-Za-z0-9_]*)="(?<path>[^"\r\n]*\.github/scripts/harness-gate\.sh)"[ \t]*$""",
                RegexOptions.CultureInvariant | RegexOptions.NonBacktracking)
            .ToDictionary(
                static match => match.Groups["variable"].Value,
                static match => match.Groups["path"].Value,
                StringComparer.Ordinal);
        foreach (var (variable, path) in assignments)
        {
            if (Regex.IsMatch(
                shell,
                "(?m)^[ \\t]*(?:[A-Za-z_][A-Za-z0-9_]*=\"[^\"\\r\\n]*\"[ \\t]+)*\"\\$"
                    + Regex.Escape(variable)
                    + "\"(?:[ \\t]+\\\\)?[ \\t]*$",
                RegexOptions.CultureInvariant | RegexOptions.NonBacktracking))
            {
                yield return $"script:{path[(path.IndexOf(".github/", StringComparison.Ordinal))..]}";
            }
        }
    }

    [Fact]
    public void ScribeContentChecksHaveOneCanonicalCommandList()
    {
        var root = TestRepositoryLayout.FindRoot();
        var canonicalPath = Path.Combine(root, ScribeContentChecksScriptPath);
        Assert.True(File.Exists(canonicalPath), $"canonical Scribe content check script is missing: {ScribeContentChecksScriptPath}");

        var canonical = File.ReadAllText(canonicalPath);
        var mathGate = File.ReadAllText(Path.Combine(root, "tools", "scripts", "workflow", "math-gate.sh"));
        var preflight = File.ReadAllText(Path.Combine(root, PreflightScriptPath));

        AssertNoUnrecognizedGateCommands(canonical, $"canonical script '{ScribeContentChecksScriptPath}'");
        var canonicalCommands = GateCommandSignatures(canonical).ToArray();
        Assert.Equal(
            [
                "projections --check --report \"$REPORT\"",
                "describe-report --check",
                "markdown-check --report \"$REPORT\" --paths-from -",
            ],
            canonicalCommands);
        Assert.Contains(ScribeContentChecksScriptPath, mathGate, StringComparison.Ordinal);
        Assert.Contains(
            "'exec /bin/bash \"$1\" \"${STRATALINT_LEAN_REPORT:?}\"'",
            mathGate,
            StringComparison.Ordinal);
        Assert.Contains(
            "export STRATALINT_SCRIBE_BASE=\"$base_sha\"",
            mathGate,
            StringComparison.Ordinal);
        Assert.Contains(ScribeContentChecksScriptPath, preflight, StringComparison.Ordinal);
        Assert.Contains(
            "STRATALINT_SCRIBE_BASE=\"$BASE_SHA\"",
            preflight,
            StringComparison.Ordinal);
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
