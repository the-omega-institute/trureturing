using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

/// <summary>
/// `lean-cache-publish.sh` 的剪枝行为:同一 config 前缀下保留最新 RETAIN 份。
/// 与主文件同为 <see cref="LeanCachePublishTests"/> 的分片(第 8 条:桶满则裂)。
/// </summary>
public sealed partial class LeanCachePublishTests
{
    /// <summary>
    /// 剪枝的合同有三条，缺一不可，而且**都只能由行为断言判**：脚本里含
    /// `prefix="lean-cache-v1-${slug}-..."` 这个字符串，对「它到底删了谁」零信息量。
    /// 这里给假 `gh` 一个四元清单——本次新建的、两份同 config 旧的、一份**别的 config**
    /// 的——然后看 `release delete` 实际收到了哪几个 tag。
    ///
    /// 三条:①同 config 的旧份被删；②本次刚建的那份**绝不**被删；③别的 config 的份
    /// **绝不**被删。第②③条是本测试存在的主要理由:一个「什么都删」的坏剪枝能通过
    /// 只测第①条的用例(放行侧天然盲，见 CLAUDE.md 变异判定条)。
    /// </summary>
    [Fact]
    public void PublishPrunesSupersededSameConfigReleasesAndSparesTheNewOneAndOtherConfigs()
    {
        const string Sha = "0123456789abcdef0123456789abcdef01234567";
        const string NewTag = "lean-cache-v1-leanprover-lean4-v4-31-0-2222222222222222-1111111111111111";
        const string SupersededA = "lean-cache-v1-leanprover-lean4-v4-31-0-2222222222222222-aaaaaaaaaaaaaaaa";
        const string SupersededB = "lean-cache-v1-leanprover-lean4-v4-31-0-2222222222222222-bbbbbbbbbbbbbbbb";
        const string RetainedC = "lean-cache-v1-leanprover-lean4-v4-31-0-2222222222222222-cccccccccccccccc";
        const string RetainedD = "lean-cache-v1-leanprover-lean4-v4-31-0-2222222222222222-dddddddddddddddd";
        const string EvictedE = "lean-cache-v1-leanprover-lean4-v4-31-0-2222222222222222-eeeeeeeeeeeeeeee";
        const string OtherConfig = "lean-cache-v1-leanprover-lean4-v4-31-0-9999999999999999-cccccccccccccccc";

        using var fixture = new PublishFixture();
        var created = Path.Combine(fixture.Bin, "created.marker");
        var deleted = Path.Combine(fixture.Bin, "deleted.txt");
        var ghArguments = Path.Combine(fixture.Bin, "..", "gh-arguments.txt");

        // 假 `gh`：`release view` 在 create 之前报不存在(脚本据此才会去创建)、之后报存在
        // (剪枝据此才敢删)。这个先后顺序本身就是被测合同的一部分。
        var gh = Path.Combine(fixture.Bin, "gh");
        File.WriteAllText(
            gh,
            "#!/usr/bin/env bash\n"
                + $"if [[ \"$1 $2\" == 'release view' ]]; then [[ -f '{created}' ]] && exit 0 || exit 1; fi\n"
                + "if [[ \"$1 $2\" == 'release create' ]]; then\n"
                + $"  printf '%s\\n' \"$@\" > '{ghArguments}'\n"
                + $"  touch '{created}'; exit 0\n"
                + "fi\n"
                + "if [[ \"$1 $2\" == 'release list' ]]; then\n"
                // 脚本以 --json tagName,createdAt + sort_by(.createdAt)|reverse 取序,
                // 故夹具供出 createdAt;此处按新→旧排列,EvictedE 最旧。
                + $"  printf '%s\\n' '{NewTag}' '{SupersededA}' '{SupersededB}'"
                + $" '{RetainedC}' '{RetainedD}' '{EvictedE}' '{OtherConfig}'\n"
                + "  exit 0\n"
                + "fi\n"
                + $"if [[ \"$1 $2\" == 'release delete' ]]; then printf '%s\\n' \"$3\" >> '{deleted}'; exit 0; fi\n"
                + "exit 0\n");
        // 走 chmod 而不是 File.SetUnixFileMode:后者带 CA1416(Windows 不支持),
        // warnaserror 下即编译失败。夹具自己的 WriteExecutable 已是这个写法。
        Assert.Equal(
            0,
            TestProcessRunner.Run(
                "chmod",
                ["+x", gh],
                Path.GetDirectoryName(gh)!,
                BoundedProcessRunner.HangDetectionBudget,
                4096).ExitCode);

        var result = fixture.RunPublish(ScriptPath(), Sha, "4242");
        Assert.Equal(0, result.ExitCode);

        var removed = File.Exists(deleted) ? File.ReadAllLines(deleted) : [];

        // ① 同 config 的旧份被删。
        // RETAIN=5:同 config 前缀下最新五份(含刚发布的 NewTag)不剪,只剪更旧的。
        Assert.DoesNotContain(SupersededA, removed);
        Assert.DoesNotContain(SupersededB, removed);
        Assert.DoesNotContain(RetainedC, removed);
        Assert.DoesNotContain(RetainedD, removed);
        Assert.Contains(EvictedE, removed);

        // ② 刚建的那份绝不被删 —— 删了它就是把一次浪费换成一次断供。
        Assert.DoesNotContain(NewTag, removed);

        // ③ 别的 config 的份绝不被删 —— 它服务的是另一条 pin，与本次无关。
        Assert.DoesNotContain(OtherConfig, removed);

        // 收据必须报出删了几份；剪枝静默就等于没有账。
        Assert.Contains("\"pruned\":1", result.Text, StringComparison.Ordinal);
    }
}
