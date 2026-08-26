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
    public void CandidateEngineeringInstallsPinnedSdkBeforeEveryDotnetCommand()
    {
        var steps = JobSteps(SharedAdmissionWorkflow, "candidate-engineering");
        var sdk = Assert.Single(
            steps.Select(static (step, index) => (Step: step, Index: index)),
            candidate => candidate.Step.Children.TryGetValue(new YamlScalarNode("uses"), out var uses)
                && uses is YamlScalarNode { Value: not null } scalar
                && scalar.Value.StartsWith("actions/setup-dotnet@", StringComparison.Ordinal));

        Assert.Equal(
            "actions/setup-dotnet@v4",
            Assert.IsType<YamlScalarNode>(sdk.Step.Children[new YamlScalarNode("uses")]).Value);
        var inputs = Assert.IsType<YamlMappingNode>(
            sdk.Step.Children[new YamlScalarNode("with")]);
        Assert.Equal(
            "candidate/global.json",
            Assert.IsType<YamlScalarNode>(
                inputs.Children[new YamlScalarNode("global-json-file")]).Value);
        Assert.False(
            sdk.Step.Children.ContainsKey(new YamlScalarNode("if")),
            "the candidate-engineering SDK setup step must not be conditionally disabled");

        var dotnetStepIndices = steps
            .Select(static (step, index) => (Step: step, Index: index))
            .Where(candidate => candidate.Step.Children.TryGetValue(
                    new YamlScalarNode("run"),
                    out var run)
                && run is YamlScalarNode { Value: not null } scalar
                && ContainsDotnetInvocation(scalar.Value))
            .ToArray();

        Assert.NotEmpty(dotnetStepIndices);
        Assert.All(
            dotnetStepIndices,
            candidate => Assert.True(
                sdk.Index < candidate.Index,
                $"the pinned SDK setup must precede dotnet command step '{StepName(candidate.Step)}'"));
    }

    [Theory]
    [InlineData("printf '%s\\n' 'dotnet is provisioned by the next step'", false)]
    [InlineData("echo 'dotnet is only mentioned here'", false)]
    [InlineData("output=\"$(dotnet build candidate/project.csproj)\"", true)]
    [InlineData("output=`dotnet build candidate/project.csproj`", true)]
    [InlineData("sh -c \"dotnet build\"", true)]
    [InlineData("printf '%s\\n' ready | dotnet restore", true)]
    [InlineData("env DOTNET_ROOT=/tmp dotnet build", true)]
    [InlineData("printf '%s\\n' ready\ndotnet test", true)]
    [InlineData("printf '%s\\n' ready && dotnet publish", true)]
    public void DotnetConsumerDetectionFailsClosedOutsideSingleQuotedLiterals(string run, bool expected)
    {
        Assert.Equal(expected, ContainsDotnetInvocation(run));
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

    private static bool ContainsDotnetInvocation(string script)
    {
        var shell = MaskSingleQuotedLiterals(script);
        return Regex.IsMatch(
            shell,
            @"(?:^|[^\w])dotnet(?:[^\w]|$)",
            RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);
    }

    private static string MaskSingleQuotedLiterals(string script)
    {
        var characters = script.ToCharArray();
        var singleQuoteStart = -1;
        var inDoubleQuote = false;
        var escaped = false;
        for (var index = 0; index < characters.Length; index++)
        {
            var character = characters[index];
            if (singleQuoteStart >= 0)
            {
                if (character != '\'') continue;

                Array.Fill(characters, ' ', singleQuoteStart, index - singleQuoteStart + 1);
                singleQuoteStart = -1;
                continue;
            }

            if (escaped)
            {
                escaped = false;
                continue;
            }

            if (character == '\\')
            {
                escaped = true;
                continue;
            }

            if (character == '"')
            {
                inDoubleQuote = !inDoubleQuote;
                continue;
            }

            if (!inDoubleQuote && character == '\'') singleQuoteStart = index;
        }

        return new string(characters);
    }

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
