using StrataLint.Engine;
using YamlDotNet.RepresentationModel;
using System.Text.RegularExpressions;

namespace StrataLint.Tests;

public sealed class AdmissionWorkflowTests
{
    private static readonly string SharedAdmissionWorkflow = AdmissionWorkflow();

    [Fact]
    public void BaselineAdmissionNeedsExactlyLeanInspect()
    {
        var workflow = AdmissionWorkflow();
        Assert.True(BaselineNeedsExactlyLeanInspect(workflow));
        var tampered = workflow.Replace("    needs: lean-inspect\n    runs-on: ubuntu-latest\n    timeout-minutes: 20",
            "    needs: [lean-inspect, some-other-job]\n    runs-on: ubuntu-latest\n    timeout-minutes: 20", StringComparison.Ordinal);
        Assert.False(BaselineNeedsExactlyLeanInspect(tampered));
    }

    // 历史方法名保留,避免删除或改名既有测试;契约已改为 merge result 的 dev 父提交。
    [Fact]
    public void DevBaselineIsTheForkPointNotTheMovingDevTip()
    {
        var workflow = AdmissionWorkflow();
        var resolve = BaselineResolutionScript(workflow);

        Assert.Contains("sha=\"$(git -C candidate rev-parse HEAD^1)\"", resolve, StringComparison.Ordinal);
        Assert.DoesNotContain("merge-base", resolve, StringComparison.Ordinal);
    }

    [Fact]
    public void AllJobsCheckoutMergeResultAndKeepPushFallback()
    {
        const string expectedRef = "${{ github.event_name == 'pull_request_target' && format('refs/pull/{0}/merge', github.event.pull_request.number) || github.sha }}";
        var workflow = SharedAdmissionWorkflow;

        foreach (var jobName in new[] { "candidate-engineering", "lean-inspect", "baseline-admission" })
        {
            var checkout = Assert.Single(
                JobSteps(workflow, jobName),
                step => step.Children.TryGetValue(new YamlScalarNode("uses"), out var uses)
                    && uses is YamlScalarNode { Value: "actions/checkout@v4" });
            var with = Assert.IsType<YamlMappingNode>(checkout.Children[new YamlScalarNode("with")]);
            var checkoutRef = Assert.IsType<YamlScalarNode>(with.Children[new YamlScalarNode("ref")]).Value;
            Assert.Equal(expectedRef, checkoutRef);
        }
    }

    [Fact]
    public void PullRequestDeltaIsDevParentToCheckedMergeResult()
    {
        var workflow = SharedAdmissionWorkflow;
        var scope = Assert.Single(
            JobSteps(workflow, "candidate-engineering"),
            step => step.Children.TryGetValue(new YamlScalarNode("id"), out var id)
                && id is YamlScalarNode { Value: "scope" });
        var scopeScript = Assert.IsType<YamlScalarNode>(
            scope.Children[new YamlScalarNode("run")]).Value ?? string.Empty;
        var baselineScript = BaselineResolutionScript(workflow);

        Assert.Contains(
            "base_sha=\"$(git -C candidate rev-parse HEAD^1)\"",
            scopeScript,
            StringComparison.Ordinal);
        Assert.Contains(
            "candidate_sha=\"$(git -C candidate rev-parse HEAD)\"",
            scopeScript,
            StringComparison.Ordinal);
        Assert.Contains(
            "git -C candidate diff --name-only -z --no-renames --diff-filter=ACDMRTUXB \"$base_sha\" \"$candidate_sha\"",
            scopeScript,
            StringComparison.Ordinal);
        Assert.DoesNotContain("merge-base", scopeScript, StringComparison.Ordinal);
        Assert.Contains(
            "sha=\"$(git -C candidate rev-parse HEAD^1)\"",
            baselineScript,
            StringComparison.Ordinal);
        Assert.DoesNotContain("merge-base", baselineScript, StringComparison.Ordinal);
        Assert.DoesNotContain("HEAD^2", scopeScript, StringComparison.Ordinal);
        Assert.DoesNotContain("HEAD^2", baselineScript, StringComparison.Ordinal);
    }

    [Fact]
    public void PushFallbackBaseIsCheckedHeadFirstParent()
    {
        var baselineScript = BaselineResolutionScript(SharedAdmissionWorkflow);

        Assert.Contains(
            "sha=\"$(git -C candidate rev-parse HEAD^1)\"",
            baselineScript,
            StringComparison.Ordinal);
        Assert.Single(Regex.Matches(
            baselineScript,
            Regex.Escape("sha=\"$(git -C candidate rev-parse HEAD^1)\"")));
        Assert.DoesNotContain("github.event.before", baselineScript, StringComparison.Ordinal);
        Assert.DoesNotContain("$GITHUB_SHA^", baselineScript, StringComparison.Ordinal);
    }

    [Fact]
    public void MissingMergeResultFailsClosedWithConflictMessage()
    {
        var workflow = SharedAdmissionWorkflow;

        foreach (var jobName in new[] { "candidate-engineering", "lean-inspect", "baseline-admission" })
        {
            var steps = JobSteps(workflow, jobName);
            var checkoutIndex = Array.FindIndex(
                steps,
                step => step.Children.TryGetValue(new YamlScalarNode("uses"), out var uses)
                    && uses is YamlScalarNode { Value: "actions/checkout@v4" });
            Assert.True(checkoutIndex >= 0 && checkoutIndex + 2 < steps.Length);

            var checkout = steps[checkoutIndex];
            Assert.Equal("checkout-merge", Assert.IsType<YamlScalarNode>(
                checkout.Children[new YamlScalarNode("id")]).Value);
            Assert.Equal("${{ github.event_name == 'pull_request_target' }}", Assert.IsType<YamlScalarNode>(
                checkout.Children[new YamlScalarNode("continue-on-error")]).Value);

            Assert.Equal("Strip checkout remote state", StepName(steps[checkoutIndex + 1]));
            var failure = steps[checkoutIndex + 2];
            Assert.Equal("Fail closed when merge result is unavailable", StepName(failure));
            var condition = Assert.IsType<YamlScalarNode>(
                failure.Children[new YamlScalarNode("if")]).Value ?? string.Empty;
            var script = Assert.IsType<YamlScalarNode>(
                failure.Children[new YamlScalarNode("run")]).Value ?? string.Empty;
            Assert.Contains("always()", condition, StringComparison.Ordinal);
            Assert.Contains("steps.checkout-merge.outcome != 'success'", condition, StringComparison.Ordinal);
            Assert.Contains("refs/pull/${{ github.event.pull_request.number }}/merge", script, StringComparison.Ordinal);
            Assert.Contains("conflicted pull requests have no merge result", script, StringComparison.Ordinal);
            Assert.Contains("admission fails closed", script, StringComparison.Ordinal);
            Assert.Contains("exit 1", script, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void CandidateEngineeringScopesPullRequestsButAlwaysRunsPushes()
    {
        var engineering = Job(AdmissionWorkflow(), "candidate-engineering");
        var steps = Assert.IsType<YamlSequenceNode>(
            engineering.Children[new YamlScalarNode("steps")]).Children
            .OfType<YamlMappingNode>()
            .ToArray();
        Assert.True(steps.Length > 3);
        Assert.Equal("Check out candidate", StepName(steps[0]));

        var scopeIndex = Array.FindIndex(
            steps,
            step => step.Children.TryGetValue(new YamlScalarNode("id"), out var id)
                && id is YamlScalarNode { Value: "scope" });
        Assert.True(scopeIndex > 0);
        var scope = steps[scopeIndex];
        Assert.Equal("scope", Assert.IsType<YamlScalarNode>(
            scope.Children[new YamlScalarNode("id")]).Value);
        var scopeScript = Assert.IsType<YamlScalarNode>(
            scope.Children[new YamlScalarNode("run")]).Value ?? string.Empty;
        Assert.Contains("git -C candidate rev-parse HEAD^1", scopeScript, StringComparison.Ordinal);
        Assert.Contains("git -C candidate rev-parse HEAD", scopeScript, StringComparison.Ordinal);
        Assert.Contains("git -C candidate diff", scopeScript, StringComparison.Ordinal);
        Assert.Contains("--no-renames", scopeScript, StringComparison.Ordinal);
        Assert.Matches(
            "(?s)if \\[\\[ \"\\$GITHUB_EVENT_NAME\" == \"push\" \\]\\]; then.*?run=\"true\"",
            scopeScript);

        var summary = steps[^1];
        Assert.Equal("Summarize candidate engineering scope", StepName(summary));
        Assert.Equal("always()", Assert.IsType<YamlScalarNode>(
            summary.Children[new YamlScalarNode("if")]).Value);
        var summaryScript = Assert.IsType<YamlScalarNode>(
            summary.Children[new YamlScalarNode("run")]).Value ?? string.Empty;
        Assert.Equal("candidate/tools/scripts/workflow/candidate-engineering-summary.sh", summaryScript);
        var extractedSummaryScript = CandidateEngineeringWorkflowFixture.SummaryScript;
        // 明细走日志、摘要只走计数:逐条路径不进 step output,因而不经 env 传给这一步。
        // 有界性本身由 WorkflowOutputBoundTests 判,这里只钉"摘要读的是计数"。
        Assert.Contains("$SCOPE_CHANGED_COUNT", extractedSummaryScript, StringComparison.Ordinal);
        Assert.Contains("$SCOPE_MATCHED_COUNT", extractedSummaryScript, StringComparison.Ordinal);
        Assert.Contains("$GITHUB_STEP_SUMMARY", extractedSummaryScript, StringComparison.Ordinal);

        Assert.Equal(
            "make -C candidate/tools dotnet",
            StepScript(steps, "Build candidate with warnings as errors"));
        Assert.Equal(
            "make -C candidate/tools test",
            StepScript(steps, "Run candidate golden and integration tests"));
        Assert.Equal(
            "make -C candidate/tools selftest",
            StepScript(steps, "Run candidate selftest twice and compare bytes"));

        Assert.All(
            steps[(scopeIndex + 1)..^1],
            step => Assert.Contains(
                "steps.scope.outputs.run == 'true'",
                Assert.IsType<YamlScalarNode>(step.Children[new YamlScalarNode("if")]).Value,
                StringComparison.Ordinal));
    }

    private static string StepScript(IEnumerable<YamlMappingNode> steps, string name)
    {
        var step = Assert.Single(steps, candidate => StepName(candidate) == name);
        return Assert.IsType<YamlScalarNode>(step.Children[new YamlScalarNode("run")]).Value
            ?? string.Empty;
    }

    // elan 从上游拉二进制,那一跳会间歇失败。两处安装都必须重试,且 elan 的缓存保存
    // 不得挂在 success() 上:装成功就该存,否则一次下载失败会让 job 红、缓存不写、
    // 下次继续 miss —— 故障自我延续。2026-08-13 实测:最近 10 个 run 里 2 个撞它,
    // dev push 上那次还连带 skip 了 admission(needs: lean-inspect)。
    [Fact]
    public void ElanInstallRetriesAndItsCacheSaveDoesNotHangOnJobSuccess()
    {
        const string installerPath = "tools/scripts/workflow/install-lean-toolchain.sh";
        var workflow = AdmissionWorkflow();
        var installer = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), installerPath));

        // 安装算法只在脚本实现一次,两个 CI 步骤都从候选树调用它。
        Assert.Single(Regex.Matches(installer, @"elan-init\.sh"));
        Assert.Single(Regex.Matches(installer, @"elan_install_with_retry\(\) \{"));
        // 数的是行首直接调用(与 Dispatch parity 扫描器同口径),不数路径字面量——
        // 调用前的具名缺席检查也引用同一路径,那不是第三次调用。
        Assert.Equal(
            2,
            Regex.Matches(
                workflow,
                "(?m)^[ \\t]*\"" + Regex.Escape($"$GITHUB_WORKSPACE/candidate/{installerPath}") + "\"",
                RegexOptions.CultureInvariant | RegexOptions.NonBacktracking).Count);
        Assert.DoesNotContain("elan-init.sh", workflow, StringComparison.Ordinal);

        // 调用形是行为投影的一部分:engineering 必须把 elan 写进 GITHUB_PATH 供后续 step 用,
        // lean-inspect 不写(它在同一 step 内自己拼 PATH)。只数调用次数抓不住这两条。
        Assert.Contains(
            $"\"$GITHUB_WORKSPACE/candidate/{installerPath}\" \"$LEAN_TOOLCHAIN_FILE\" --github-path \"$GITHUB_PATH\"",
            workflow,
            StringComparison.Ordinal);
        Assert.Contains(
            $"\"$GITHUB_WORKSPACE/candidate/{installerPath}\" candidate/lean-toolchain\n",
            workflow,
            StringComparison.Ordinal);

        // 工具链下载是第二个网络跳,单独失败过(releases.lean-lang.org 返回空响应),
        // 所以它也必须走重试,而不是裸 `elan toolchain install`。
        Assert.Single(Regex.Matches(installer, @"elan_toolchain_with_retry\(\) \{"));
        Assert.DoesNotContain("\"$HOME/.elan/bin/elan\" toolchain install \"$toolchain\"", installer, StringComparison.Ordinal);

        // 每一处 ~/.elan 的 restore 都必须有前缀回退。两个 job 的精确 key 由不同表达式算出
        // (单文件 sha256 vs hashFiles 两文件),永不相等;没有回退,写入方存的缓存读取方
        // 就够不着,于是每轮都联网重下工具链。实测:仓库里有 695MB 的 elan 缓存,而
        // engineering job 从来没命中过。
        // 用 YAML 解析而非正则:step 里的注释会打断任何「key 紧跟 restore-keys」的文本假设。
        var elanRestores = Jobs(workflow).Children.Values
            .OfType<YamlMappingNode>()
            .Where(job => job.Children.ContainsKey(new YamlScalarNode("steps")))
            .SelectMany(job => ((YamlSequenceNode)job.Children[new YamlScalarNode("steps")])
                .Children.OfType<YamlMappingNode>())
            .Where(step => step.Children.TryGetValue(new YamlScalarNode("uses"), out var uses)
                && uses is YamlScalarNode { Value: not null } u
                && u.Value.StartsWith("actions/cache/restore@", StringComparison.Ordinal))
            .Where(step => step.Children.TryGetValue(new YamlScalarNode("with"), out var with)
                && with is YamlMappingNode w
                && w.Children.TryGetValue(new YamlScalarNode("path"), out var path)
                && path is YamlScalarNode { Value: "~/.elan" })
            .Select(step => (YamlMappingNode)step.Children[new YamlScalarNode("with")])
            .ToArray();

        Assert.Equal(2, elanRestores.Length);
        Assert.All(
            elanRestores,
            with => Assert.True(
                with.Children.ContainsKey(new YamlScalarNode("restore-keys")),
                "an ~/.elan restore without restore-keys can never reach the cache the other job wrote"));

        // 用 YAML 解析而非正则:步骤上方的注释会把「name 紧跟 if」的文本假设打断。
        var leanInspect = Assert.IsType<YamlMappingNode>(
            Jobs(workflow).Children[new YamlScalarNode("lean-inspect")]);
        var steps = Assert.IsType<YamlSequenceNode>(
            leanInspect.Children[new YamlScalarNode("steps")]);
        var save = Assert.Single(
            steps.Children.OfType<YamlMappingNode>(),
            node => node.Children.TryGetValue(new YamlScalarNode("name"), out var name)
                && name is YamlScalarNode { Value: not null } scalar
                && scalar.Value.StartsWith("Save elan toolchains", StringComparison.Ordinal));
        var condition = Assert.IsType<YamlScalarNode>(
            save.Children[new YamlScalarNode("if")]).Value ?? string.Empty;
        Assert.DoesNotContain("success()", condition, StringComparison.Ordinal);
        Assert.Contains("always()", condition, StringComparison.Ordinal);
    }

    [Fact]
    public void LeanToolchainInstallerHonorsAttemptsAndGithubPath()
    {
        if (OperatingSystem.IsWindows()) return;

        var root = TestRepositoryLayout.FindRoot();
        var installer = Path.Combine(root, "tools", "scripts", "workflow", "install-lean-toolchain.sh");
        using var fixture = new TemporaryDirectory();
        var home = Path.Combine(fixture.Path, "home");
        var elanBin = Path.Combine(home, ".elan", "bin");
        var stubBin = Path.Combine(fixture.Path, "bin");
        var attempts = Path.Combine(fixture.Path, "attempts.log");
        var githubPath = Path.Combine(fixture.Path, "github-path");
        var toolchain = Path.Combine(fixture.Path, "lean-toolchain");
        Directory.CreateDirectory(elanBin);
        Directory.CreateDirectory(stubBin);
        File.WriteAllText(toolchain, "leanprover/lean4:v4.24.0\n");
        File.WriteAllText(
            Path.Combine(elanBin, "elan"),
            "#!/usr/bin/env bash\n"
                + "if [[ \"${1:-}\" == toolchain && \"${2:-}\" == list ]]; then exit 0; fi\n"
                + "if [[ \"${1:-}\" == toolchain && \"${2:-}\" == install ]]; then printf 'attempt\\n' >> \"$ATTEMPTS_LOG\"; exit 42; fi\n"
                + "exit 0\n");
        File.WriteAllText(Path.Combine(stubBin, "sleep"), "#!/usr/bin/env bash\nexit 0\n");
        File.SetUnixFileMode(
            Path.Combine(elanBin, "elan"),
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        File.SetUnixFileMode(
            Path.Combine(stubBin, "sleep"),
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);

        var result = BoundedProcessRunner.Run(
            "env",
            [
                $"HOME={home}",
                $"PATH={stubBin}:{Environment.GetEnvironmentVariable("PATH")}",
                $"ATTEMPTS_LOG={attempts}",
                "/bin/bash",
                installer,
                toolchain,
                "--attempts",
                "2",
                "--github-path",
                githubPath,
            ],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        Assert.Equal(1, result.ExitCode);
        Assert.Equal(2, File.ReadAllLines(attempts).Length);
        Assert.Equal($"{elanBin}\n", File.ReadAllText(githubPath));
    }

    private static string BaselineResolutionScript(string workflow)
    {
        var leanInspect = Assert.IsType<YamlMappingNode>(
            Jobs(workflow).Children[new YamlScalarNode("lean-inspect")]);
        var steps = Assert.IsType<YamlSequenceNode>(
            leanInspect.Children[new YamlScalarNode("steps")]);
        var step = Assert.Single(
            steps.Children.OfType<YamlMappingNode>(),
            node => node.Children.TryGetValue(new YamlScalarNode("id"), out var id)
                && id is YamlScalarNode { Value: "base" });
        return Assert.IsType<YamlScalarNode>(step.Children[new YamlScalarNode("run")]).Value ?? string.Empty;
    }

    [Fact]
    public void RunsCompleteMathematicalChecksAfterProducingLiveReport()
    {
        var root = TestRepositoryLayout.FindRoot();
        var workflow = File.ReadAllText(Path.Combine(root, ".github", "workflows", "ci.yml"));
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var document = Assert.IsType<YamlMappingNode>(stream.Documents[0].RootNode);
        var jobs = Assert.IsType<YamlMappingNode>(document.Children[new YamlScalarNode("jobs")]);
        var leanInspect = Assert.IsType<YamlMappingNode>(jobs.Children[new YamlScalarNode("lean-inspect")]);
        var steps = Assert.IsType<YamlSequenceNode>(leanInspect.Children[new YamlScalarNode("steps")]);
        var namedSteps = steps.Children.OfType<YamlMappingNode>()
            .Select(static step => new
            {
                Node = step,
                Name = Assert.IsType<YamlScalarNode>(step.Children[new YamlScalarNode("name")]).Value,
            })
            .ToArray();
        var reportIndex = Array.FindIndex(namedSteps, static step =>
            step.Name == "Produce source-bound canonical Lean reports");
        var reconciliationIndex = Array.FindIndex(namedSteps, static step =>
            step.Name == "Run complete mathematical content checks");
        Assert.True(reportIndex >= 0, "admission must produce the canonical live Lean report");
        Assert.True(reconciliationIndex > reportIndex, "mathematical checks must run after report production");

        var reconciliation = namedSteps[reconciliationIndex].Node;
        var run = Assert.IsType<YamlScalarNode>(reconciliation.Children[new YamlScalarNode("run")]).Value!;
        Assert.Contains("tools/scripts/workflow/scribe-content-checks.sh", run, StringComparison.Ordinal);
        Assert.Contains("steps.base.outputs.sha", run, StringComparison.Ordinal);
        Assert.Contains("\"$report\" \"$scribe\" \"$base\"", run, StringComparison.Ordinal);
        Assert.Contains(".judge-binaries/scribe/StrataLint.Scribe.dll", run, StringComparison.Ordinal);
        Assert.DoesNotContain("--changes-file", run, StringComparison.Ordinal);
        Assert.DoesNotContain("--producer-paths-file", run, StringComparison.Ordinal);
        Assert.DoesNotContain("dotnet test", run, StringComparison.Ordinal);
        Assert.DoesNotContain("tools/tests", run, StringComparison.Ordinal);
    }

    [Fact]
    public void JudgeBinaryCacheIsSharedByEngineeringAndBothContentJobs()
    {
        var workflow = AdmissionWorkflow();
        var cacheKeyLines = workflow.Split('\n')
            .Where(static line => line.TrimStart().StartsWith(
                "key: stratalint-judge-binaries-v1-",
                StringComparison.Ordinal))
            .Select(static line => line.Trim())
            .Distinct(StringComparer.Ordinal)
            .ToArray();

        Assert.Single(cacheKeyLines);
        Assert.Equal(2, Regex.Matches(workflow, "- name: Restore judge binaries").Count);
        Assert.Equal(3, Regex.Matches(
            workflow,
            "- name: Resolve judge binary content address before build outputs exist").Count);
        Assert.Equal(3, Regex.Matches(workflow, "hashFiles\\('candidate/tools/\\*\\*'").Count);
        Assert.Equal(3, Regex.Matches(workflow, "'candidate/Blueprint/\\*\\*/\\*.scribe.cs'").Count);
        Assert.Equal(3, Regex.Matches(workflow, "'candidate/Directory.\\*'").Count);
        Assert.Equal(3, Regex.Matches(workflow, "'candidate/global.json'").Count);

        var engineering = JobText(workflow, "candidate-engineering", "lean-inspect");
        var leanInspect = JobText(workflow, "lean-inspect", "baseline-admission");
        var admission = workflow[workflow.IndexOf("  baseline-admission:", StringComparison.Ordinal)..];
        Assert.Contains("dotnet publish", engineering, StringComparison.Ordinal);
        Assert.Contains("github.event_name == 'push'", engineering, StringComparison.Ordinal);
        Assert.Contains("github.ref == 'refs/heads/dev'", engineering, StringComparison.Ordinal);
        Assert.Contains("actions/cache/save@v4", engineering, StringComparison.Ordinal);
        Assert.Contains("actions/cache/restore@v4", leanInspect, StringComparison.Ordinal);
        Assert.Contains("dotnet build candidate/tools/StrataLint.Scribe/StrataLint.Scribe.csproj", leanInspect, StringComparison.Ordinal);
        Assert.DoesNotContain("dotnet test", leanInspect, StringComparison.Ordinal);
        Assert.Contains("actions/cache/restore@v4", admission, StringComparison.Ordinal);
        Assert.Contains("--judge-dll", admission, StringComparison.Ordinal);
    }

    private static string JobText(string workflow, string job, string nextJob)
    {
        var start = workflow.IndexOf($"  {job}:\n", StringComparison.Ordinal);
        var end = workflow.IndexOf($"  {nextJob}:\n", start, StringComparison.Ordinal);
        Assert.True(start >= 0 && end > start);
        return workflow[start..end];
    }

    private static string AdmissionWorkflow() =>
        File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), ".github", "workflows", "ci.yml"));

    private static YamlMappingNode Jobs(string workflow)
    {
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var document = Assert.IsType<YamlMappingNode>(stream.Documents[0].RootNode);
        return Assert.IsType<YamlMappingNode>(document.Children[new YamlScalarNode("jobs")]);
    }

    private static YamlMappingNode Job(string workflow, string job) =>
        Assert.IsType<YamlMappingNode>(Jobs(workflow).Children[new YamlScalarNode(job)]);

    private static YamlMappingNode[] JobSteps(string workflow, string job) =>
        Assert.IsType<YamlSequenceNode>(Job(workflow, job).Children[new YamlScalarNode("steps")])
            .Children
            .OfType<YamlMappingNode>()
            .ToArray();

    private static string StepName(YamlMappingNode step) =>
        Assert.IsType<YamlScalarNode>(step.Children[new YamlScalarNode("name")]).Value ?? string.Empty;

    private static bool BaselineNeedsExactlyLeanInspect(string workflow) =>
        Needs(Job(workflow, "baseline-admission")).SequenceEqual(["lean-inspect"], StringComparer.Ordinal);

    private static IEnumerable<string> Needs(YamlMappingNode job)
    {
        if (!job.Children.TryGetValue(new YamlScalarNode("needs"), out var needs)) yield break;
        if (needs is YamlScalarNode scalar)
        {
            yield return scalar.Value!;
            yield break;
        }
        foreach (var item in Assert.IsType<YamlSequenceNode>(needs).Children.OfType<YamlScalarNode>())
            yield return item.Value!;
    }

}

public sealed class CandidateEngineeringExecutionTests
{
    [Fact]
    public void CandidateEngineeringTestsProduceAndVerifyExecutionEvidence()
    {
        if (OperatingSystem.IsWindows()) return;

        var result = CandidateEngineeringWorkflowWitness.Execute();

        Assert.True(
            result.ExitCode == 0 && result.Verified && result.FailurePropagates,
            $"execution evidence was not verified or its failure was suppressed\nstdout:\n{result.StandardOutput}\nstderr:\n{result.StandardError}");
    }
}

public sealed class CandidateEngineeringReachabilityTests
{
    [Fact]
    public void CandidateEngineeringReachabilityFollowsEveryTransitiveNeed()
    {
        const string workflow = """
            on:
              push:
              pull_request_target:
            jobs:
              skipped-root:
                if: github.event_name == 'workflow_dispatch'
              middle:
                needs: skipped-root
              candidate-engineering:
                needs: middle
            """;

        var result = CandidateEngineeringWorkflowWitness.CheckReachability(workflow);

        Assert.False(result.IsReachable);
        Assert.Contains("candidate-engineering -> middle -> skipped-root", result.Reason, StringComparison.Ordinal);
    }

    [Fact]
    public void CandidateEngineeringReachabilityFailsClosedForUndecidableCondition()
    {
        const string workflow = """
            on: push
            jobs:
              guarded:
                if: github.actor == 'octocat'
              candidate-engineering:
                needs: guarded
            """;

        var result = CandidateEngineeringWorkflowWitness.CheckReachability(workflow);

        Assert.False(result.IsReachable);
        Assert.Contains("undecidable", result.Reason, StringComparison.Ordinal);
    }
}

internal static class CandidateEngineeringWorkflowWitness
{
    internal sealed record Result(
        int ExitCode, bool Verified, bool FailurePropagates, string StandardOutput, string StandardError);

    internal static CandidateEngineeringReachabilityWitness.Result CheckReachability(string workflow) =>
        CandidateEngineeringReachabilityWitness.Check(workflow);

    internal static Result Execute()
    {
        if (OperatingSystem.IsWindows()) throw new PlatformNotSupportedException();

        var workflow = WorkflowText();
        var reachability = CheckReachability(workflow);
        if (!reachability.IsReachable)
        {
            return new Result(-1, false, false, "", reachability.Reason);
        }

        var job = EngineeringJob(workflow);
        if (!Condition(Scalar(job, "if"), defaultWhenEmpty: true))
        {
            return new Result(-1, false, false, "", "candidate-engineering job was skipped");
        }

        var steps = Steps(job);
        var producer = Step(steps, "id", "engineering-tests");
        var verifier = Step(steps, "name", "Summarize candidate engineering scope");
        const string verifierCommand = "candidate/tools/scripts/workflow/candidate-engineering-summary.sh";
        if (!string.Equals(Scalar(verifier, "run"), verifierCommand, StringComparison.Ordinal))
        {
            return new Result(-1, false, false, "", "verifier did not invoke the extracted summary script");
        }
        if (!string.Equals(Scalar(verifier, "shell"), "bash", StringComparison.Ordinal))
        {
            return new Result(-1, false, false, "", "verifier shell is not canonical bash");
        }

        using var directory = new TemporaryDirectory();
        var candidateTools = Path.Combine(directory.Path, "candidate", "tools");
        var bin = Path.Combine(directory.Path, "bin");
        Directory.CreateDirectory(candidateTools);
        File.Copy(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools", "Makefile"),
            Path.Combine(candidateTools, "Makefile"));
        CandidateEngineeringWorkflowFixture.InstallSummaryScript(candidateTools);
        Directory.CreateDirectory(bin);
        var dotnet = Path.Combine(bin, "dotnet");
        File.WriteAllText(
            dotnet,
            "#!/usr/bin/env bash\nexit 0\n");
        File.SetUnixFileMode(
            dotnet,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);

        var producerOutcome = "skipped";
        if (Condition(Scalar(producer, "if")))
        {
            var output = Run(
                Scalar(producer, "run"),
                directory.Path,
                bin,
                Environment(producer, directory.Path, producerOutcome));
            producerOutcome = output.ExitCode == 0 ? "success" : "failure";
        }

        if (!Condition(Scalar(verifier, "if")))
        {
            return new Result(-1, false, false, "", "verifier was skipped");
        }

        var verifierOutput = Run(
            Scalar(verifier, "run"),
            directory.Path,
            bin,
            Environment(verifier, directory.Path, producerOutcome));
        var verified = Read(Path.Combine(directory.Path, "summary"))
            .Contains("- Engineering test execution: verified\n", StringComparison.Ordinal);
        var receipt = Path.Combine(directory.Path, "candidate-engineering-tests.receipt");
        File.Delete(receipt);
        var enforcementOutput = Run(
            Scalar(verifier, "run"),
            directory.Path,
            bin,
            Environment(verifier, directory.Path, "success"));
        var failurePropagates = enforcementOutput.ExitCode != 0
            && !Condition(Scalar(verifier, "continue-on-error"));
        return new Result(
            verifierOutput.ExitCode,
            verified,
            failurePropagates,
            System.Text.Encoding.UTF8.GetString(verifierOutput.StandardOutput)
                + System.Text.Encoding.UTF8.GetString(enforcementOutput.StandardOutput),
            System.Text.Encoding.UTF8.GetString(verifierOutput.StandardError)
                + System.Text.Encoding.UTF8.GetString(enforcementOutput.StandardError));
    }

    private static ProcessOutput Run(
        string script,
        string root,
        string bin,
        IEnumerable<string> environment) =>
        BoundedProcessRunner.Run(
            "env",
            [$"PATH={bin}:/usr/bin:/bin", $"RUNNER_TEMP={root}", $"GITHUB_STEP_SUMMARY={Path.Combine(root, "summary")}",
                .. environment, "/bin/bash", "--noprofile", "--norc", "-e", "-o", "pipefail", "-c", script],
            root,
            TimeSpan.FromSeconds(10),
            16 * 1024);

    private static IEnumerable<string> Environment(YamlMappingNode step, string root, string outcome)
    {
        var environment = (YamlMappingNode)step.Children[new YamlScalarNode("env")];
        foreach (var item in environment.Children)
        {
            var key = ((YamlScalarNode)item.Key).Value!;
            var value = ((YamlScalarNode)item.Value).Value!;
            yield return key + "=" + value
                .Replace("${{ runner.temp }}", root, StringComparison.Ordinal)
                .Replace("${{ steps.engineering-tests.outcome }}", outcome, StringComparison.Ordinal)
                .Replace("${{ steps.scope.outputs.run }}", "true", StringComparison.Ordinal);
        }
    }

    private static bool Condition(string condition, bool defaultWhenEmpty = false)
    {
        if (string.IsNullOrWhiteSpace(condition)) return defaultWhenEmpty;
        return condition
            .Replace("${{", "", StringComparison.Ordinal)
            .Replace("}}", "", StringComparison.Ordinal)
            .Split("&&", StringSplitOptions.TrimEntries)
            .All(static term => term is "true" or "always()" or "steps.scope.outputs.run == 'true'");
    }

    private static string WorkflowText() => File.ReadAllText(Path.Combine(
        TestRepositoryLayout.FindRoot(), ".github", "workflows", "ci.yml"));

    private static YamlMappingNode EngineeringJob(string workflow)
    {
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var root = Assert.IsType<YamlMappingNode>(stream.Documents.Single().RootNode);
        var jobs = (YamlMappingNode)root.Children[new YamlScalarNode("jobs")];
        return (YamlMappingNode)jobs.Children[new YamlScalarNode("candidate-engineering")];
    }

    private static YamlMappingNode[] Steps(YamlMappingNode job) =>
        ((YamlSequenceNode)job.Children[new YamlScalarNode("steps")]).Children
            .OfType<YamlMappingNode>().ToArray();

    private static YamlMappingNode Step(IEnumerable<YamlMappingNode> steps, string key, string value) =>
        steps.Single(step => Scalar(step, key) == value);

    private static string Scalar(YamlMappingNode node, string key) =>
        node.Children.TryGetValue(new YamlScalarNode(key), out var value)
            ? ((YamlScalarNode)value).Value ?? string.Empty
            : string.Empty;

    private static string Read(string path) => File.Exists(path) ? File.ReadAllText(path) : string.Empty;
}

internal static class CandidateEngineeringWorkflowFixture
{
    internal static string SummaryScript => File.ReadAllText(Path.Combine(
        TestRepositoryLayout.FindRoot(), "tools", "scripts", "workflow", "candidate-engineering-summary.sh"));

    internal static void InstallSummaryScript(string candidateTools)
    {
        if (OperatingSystem.IsWindows()) throw new PlatformNotSupportedException();

        var workflowScripts = Path.Combine(candidateTools, "scripts", "workflow");
        Directory.CreateDirectory(workflowScripts);
        var destination = Path.Combine(workflowScripts, "candidate-engineering-summary.sh");
        File.Copy(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools", "scripts", "workflow", "candidate-engineering-summary.sh"),
            destination);
        File.SetUnixFileMode(
            destination,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
    }
}
