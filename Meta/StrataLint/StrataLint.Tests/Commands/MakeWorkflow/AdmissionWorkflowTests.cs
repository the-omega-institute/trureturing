using YamlDotNet.RepresentationModel;
using System.Text.RegularExpressions;

namespace StrataLint.Tests;

public sealed class AdmissionWorkflowTests
{
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
    // 分叉点同时让法官二进制、冻结账本与 --baseline-lean-report 取自同一棵树,
    // 因此不会重演 PR #1144(同一份 report 被要求同时是两棵树的 report)。
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
                && id is YamlScalarNode { Value: "baseline" });
        return Assert.IsType<YamlScalarNode>(step.Children[new YamlScalarNode("run")]).Value ?? string.Empty;
    }

    [Fact]
    public void InstallsCanonicalReportAndRunsProjectionChecksAfterProducingLiveReport()
    {
        var root = FindRepositoryRoot();
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
            step.Name == "Install canonical Lean report and run projection checks");
        Assert.True(reportIndex >= 0, "admission must produce the canonical live Lean report");
        Assert.True(reconciliationIndex > reportIndex, "reconciliation must run after report production");

        var reconciliation = namedSteps[reconciliationIndex].Node;
        var run = Assert.IsType<YamlScalarNode>(reconciliation.Children[new YamlScalarNode("run")]).Value!;
        Assert.Contains("make -C candidate test", run, StringComparison.Ordinal);
        Assert.DoesNotContain("--filter", run, StringComparison.Ordinal);
        Assert.DoesNotContain("python3 -c", run, StringComparison.Ordinal);
        Assert.Contains("report-consumer.sh", run, StringComparison.Ordinal);
        Assert.Contains("--bundle-suffixes", run, StringComparison.Ordinal);
    }

    private static string AdmissionWorkflow() =>
        File.ReadAllText(Path.Combine(FindRepositoryRoot(), ".github", "workflows", "ci.yml"));

    private static YamlMappingNode Jobs(string workflow)
    {
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var document = Assert.IsType<YamlMappingNode>(stream.Documents[0].RootNode);
        return Assert.IsType<YamlMappingNode>(document.Children[new YamlScalarNode("jobs")]);
    }

    private static YamlMappingNode Job(string workflow, string job) =>
        Assert.IsType<YamlMappingNode>(Jobs(workflow).Children[new YamlScalarNode(job)]);

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

    private static string FindRepositoryRoot()
    {
        for (var directory = new DirectoryInfo(AppContext.BaseDirectory);
             directory is not null;
             directory = directory.Parent)
        {
            if (File.Exists(Path.Combine(directory.FullName, "lakefile.toml")))
                return directory.FullName;
        }

        throw new InvalidOperationException("Repository root was not found.");
    }
}
