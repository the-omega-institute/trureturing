using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.ScriptTests;

public sealed partial class RootMakefileTests
{
    [Fact(DisplayName = "Makefile and inspector dispatch counts are pinned in the thin dispatch table")]
    public void MakefileIsAThinCompleteDispatchTable()
    {
        var makefile = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("Makefile"));

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
        var mathGate = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/scripts/workflow/math-gate.sh"));
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
        var warmDonor = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/scripts/worktree/warm-donor.sh"));
        Assert.Contains("git pull --ff-only origin dev", warmDonor, StringComparison.Ordinal);
        Assert.Contains("make -C \"$ROOT\" lean", warmDonor, StringComparison.Ordinal);
        Assert.DoesNotContain("lsof", warmDonor, StringComparison.Ordinal);
        Assert.DoesNotContain("LeanCacheBusyProbe", warmDonor, StringComparison.Ordinal);
        foreach (var excludedText in new[]
        {
            TestRepositoryLayout.ReadAllText(
                RepositoryRelativePath.Create("tools/scripts/worktree-init.sh")),
            TestRepositoryLayout.ReadAllText(
                RepositoryRelativePath.Create("tools/scripts/worktree/lean-cache-ensure.sh")),
            TestRepositoryLayout.ReadAllText(
                RepositoryRelativePath.Create(".github/workflows/ci.yml")),
            TestRepositoryLayout.ReadAllText(
                RepositoryRelativePath.Create("tools/scripts/preflight.sh")),
            TestRepositoryLayout.ReadAllText(
                RepositoryRelativePath.Create("tools/scripts/workflow/math-gate.sh")),
            TestRepositoryLayout.ReadAllText(
                RepositoryRelativePath.Create("tools/scripts/local-harness-gate.sh")),
        })
        {
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
        var inspector = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/lean-inspector/inspect.sh"));
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
        var cacheEnsure = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/scripts/worktree/lean-cache-ensure.sh"));
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
        var theoryCandidatesRecipe = Recipe(makefile, "theory-candidates");
        Assert.Contains("dotnet run --no-build --project", theoryCandidatesRecipe, StringComparison.Ordinal);
        Assert.Contains(" theory-candidates", theoryCandidatesRecipe, StringComparison.Ordinal);
        Assert.Contains(
            "--owner-override-file \"$(OWNER_OVERRIDE_FILE)\"",
            theoryCandidatesRecipe,
            StringComparison.Ordinal);
        Assert.DoesNotContain("OWNER_OVERRIDE)", theoryCandidatesRecipe, StringComparison.Ordinal);
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
        var makefile = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("Makefile"));
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
}
