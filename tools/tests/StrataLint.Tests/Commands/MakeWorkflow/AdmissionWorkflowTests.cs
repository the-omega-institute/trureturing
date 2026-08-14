using YamlDotNet.RepresentationModel;
using System.Diagnostics;
using System.Text.RegularExpressions;

namespace StrataLint.Tests;

public sealed class AdmissionWorkflowTests
{
    private const string ProjectionTest =
        "StrataLint.Scribe.Tests.StatementProjectionPilotTests.LiveReportMatchesPinnedFixtureWhenAvailable";
    private const string DocumentTest =
        "StrataLint.Scribe.Tests.DocumentDiscoveryTests.GeneratedMarkdownIsDeterministicAndMatchesTheCommittedTree";

    [Fact]
    public void BaselineAdmissionNeedsExactlyLeanInspect()
    {
        var workflow = AdmissionWorkflow();
        Assert.True(BaselineNeedsExactlyLeanInspect(workflow));
        var tampered = workflow.Replace("    needs: lean-inspect\n    runs-on: ubuntu-latest\n    timeout-minutes: 20",
            "    needs: [lean-inspect, some-other-job]\n    runs-on: ubuntu-latest\n    timeout-minutes: 20", StringComparison.Ordinal);
        Assert.False(BaselineNeedsExactlyLeanInspect(tampered));
    }

    // 法官那棵树必须是候选的分叉点,不是 dev 的当前 tip。用 tip 会让在飞的 PR 被
    // 分叉之后才落地的规则追溯判决:候选没碰的东西,却要按它没见过的规则受审。
    // 分叉点让 append-only 规则只问候选从哪里出发,不会把 dev 后加的条目归罪于候选。
    [Fact]
    public void DevBaselineIsTheForkPointNotTheMovingDevTip()
    {
        var workflow = AdmissionWorkflow();
        var resolve = BaselineResolutionScript(workflow);

        Assert.Contains("merge-base", resolve, StringComparison.Ordinal);
        Assert.DoesNotContain(
            "sha=\"${{ github.event.pull_request.base.sha }}\"",
            resolve,
            StringComparison.Ordinal);
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

        var scope = steps[1];
        Assert.Equal("scope", Assert.IsType<YamlScalarNode>(
            scope.Children[new YamlScalarNode("id")]).Value);
        var scopeScript = Assert.IsType<YamlScalarNode>(
            scope.Children[new YamlScalarNode("run")]).Value ?? string.Empty;
        Assert.Contains("merge-base", scopeScript, StringComparison.Ordinal);
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
        Assert.Contains("$SCOPE_PATHS", summaryScript, StringComparison.Ordinal);
        Assert.Contains("$GITHUB_STEP_SUMMARY", summaryScript, StringComparison.Ordinal);

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
            steps[2..^1],
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
        var workflow = AdmissionWorkflow();

        // 每一处 elan 安装都必须被一个重试循环包住 —— 数的是「安装点」与「重试循环」
        // 的配对,不是某个标识符出现几次(函数定义与调用各算一次会把计数弄错)。
        var installs = Regex.Matches(workflow, @"elan-init\.sh").Count;
        Assert.Equal(2, installs);
        Assert.Equal(installs, Regex.Matches(workflow, @"elan_install_with_retry\(\) \{").Count);

        // 工具链下载是第二个网络跳,单独失败过(releases.lean-lang.org 返回空响应),
        // 所以它也必须走重试,而不是裸 `elan toolchain install`。
        Assert.Equal(installs, Regex.Matches(workflow, @"elan_toolchain_with_retry\(\) \{").Count);
        Assert.DoesNotContain("\"$HOME/.elan/bin/elan\" toolchain install \"$toolchain\"", workflow, StringComparison.Ordinal);

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
    public void ReconcilesStatementProjectionAfterProducingLiveReport()
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
            step.Name == "Reconcile pinned statement projections with live Lean report");
        Assert.True(reportIndex >= 0, "admission must produce the canonical live Lean report");
        Assert.True(reconciliationIndex > reportIndex, "reconciliation must run after report production");

        var reconciliation = namedSteps[reconciliationIndex].Node;
        var environment = Assert.IsType<YamlMappingNode>(reconciliation.Children[new YamlScalarNode("env")]);
        Assert.Equal("1", Assert.IsType<YamlScalarNode>(
            environment.Children[new YamlScalarNode("STRATALINT_REQUIRE_LIVE_REPORT")]).Value);
        var run = Assert.IsType<YamlScalarNode>(reconciliation.Children[new YamlScalarNode("run")]).Value!;
        var expectedTests = new HashSet<string>(StringComparer.Ordinal)
        {
            ProjectionTest,
            DocumentTest,
        };
        var filterTests = Regex.Matches(run, @"FullyQualifiedName=([^|'\s]+)")
            .Select(static match => match.Groups[1].Value)
            .ToHashSet(StringComparer.Ordinal);
        var pythonExpectedBlock = Regex.Match(
            run,
            @"(?s)expected\s*=\s*\{(?<body>.*?)\}",
            RegexOptions.CultureInvariant);
        Assert.True(pythonExpectedBlock.Success, "the TRX validator must declare its expected test-name set");
        var validatorTests = Regex.Matches(pythonExpectedBlock.Groups["body"].Value, "[\"'](?<name>[^\"']+)[\"']")
            .Select(static match => match.Groups["name"].Value)
            .ToHashSet(StringComparer.Ordinal);

        Assert.Equal(expectedTests.Order(), filterTests.Order());
        Assert.Equal(expectedTests.Order(), validatorTests.Order());
        Assert.Equal(filterTests.Order(), validatorTests.Order());
        Assert.Contains("--logger \"trx;LogFileName=$results\"", run, StringComparison.Ordinal);
        Assert.Contains("len(results) != 2", run, StringComparison.Ordinal);
        Assert.Contains("set(names) != expected", run, StringComparison.Ordinal);
    }

    public static TheoryData<string, string?> RejectedTrxReports => new()
    {
        { "missing file", null },
        { "empty file", "" },
        { "invalid XML", "not xml" },
        { "non-Passed outcome", Trx((ProjectionTest, "Passed"), (DocumentTest, "NotExecuted")) },
        { "one result", Trx((ProjectionTest, "Passed")) },
        { "three results", Trx((ProjectionTest, "Passed"), (DocumentTest, "Passed"), ("Extra.Test", "Passed")) },
        { "duplicate name", Trx((ProjectionTest, "Passed"), (ProjectionTest, "Passed")) },
        { "different name set", Trx((ProjectionTest, "Passed"), ("Wrong.Test", "Passed")) },
    };

    [Theory]
    [MemberData(nameof(RejectedTrxReports))]
    public void TrxValidatorRejectsInvalidReports(string _, string? trx)
    {
        Assert.NotEqual(0, RunTrxValidator(trx));
    }

    [Fact]
    public void TrxValidatorAcceptsExactlyTheExpectedPassingReports()
    {
        Assert.Equal(0, RunTrxValidator(Trx((ProjectionTest, "Passed"), (DocumentTest, "Passed"))));
    }

    private static int RunTrxValidator(string? trx)
    {
        var run = ReconciliationRun();
        var scriptMatch = Regex.Match(
            run,
            "(?s)python3 -c '(?<script>.*?)' \\\"\\$results\\\"",
            RegexOptions.CultureInvariant);
        Assert.True(scriptMatch.Success, "the reconciliation step must invoke its embedded TRX validator");

        var temporaryDirectory = Path.Combine(Path.GetTempPath(), $"stratalint-trx-validator-{Guid.NewGuid():N}");
        Directory.CreateDirectory(temporaryDirectory);
        try
        {
            var trxPath = Path.Combine(temporaryDirectory, "results.trx");
            if (trx is not null)
                File.WriteAllText(trxPath, trx);
            var startInfo = new ProcessStartInfo
            {
                FileName = "python3",
                RedirectStandardError = true,
                RedirectStandardOutput = true,
                UseShellExecute = false,
            };
            startInfo.ArgumentList.Add("-c");
            startInfo.ArgumentList.Add(scriptMatch.Groups["script"].Value);
            startInfo.ArgumentList.Add(trxPath);
            using var process = Process.Start(startInfo)!;
            process.WaitForExit();
            return process.ExitCode;
        }
        finally
        {
            Directory.Delete(temporaryDirectory, recursive: true);
        }
    }

    private static string Trx(params (string Name, string Outcome)[] results) =>
        "<TestRun><Results>" + string.Concat(results.Select(static result =>
            $"<UnitTestResult testName=\"{result.Name}\" outcome=\"{result.Outcome}\" />")) + "</Results></TestRun>";

    private static string ReconciliationRun()
    {
        var workflow = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), ".github", "workflows", "ci.yml"));
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var document = Assert.IsType<YamlMappingNode>(stream.Documents[0].RootNode);
        var jobs = Assert.IsType<YamlMappingNode>(document.Children[new YamlScalarNode("jobs")]);
        var leanInspect = Assert.IsType<YamlMappingNode>(jobs.Children[new YamlScalarNode("lean-inspect")]);
        var steps = Assert.IsType<YamlSequenceNode>(leanInspect.Children[new YamlScalarNode("steps")]);
        var reconciliation = steps.Children.OfType<YamlMappingNode>().Single(step =>
            Assert.IsType<YamlScalarNode>(step.Children[new YamlScalarNode("name")]).Value ==
            "Reconcile pinned statement projections with live Lean report");
        return Assert.IsType<YamlScalarNode>(reconciliation.Children[new YamlScalarNode("run")]).Value!;
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
