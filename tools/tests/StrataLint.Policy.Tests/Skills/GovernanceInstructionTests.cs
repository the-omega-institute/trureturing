using System.Text;

namespace StrataLint.Policy.Tests;

public sealed class GovernanceInstructionTests
{
    [Fact]
    public void DigestionDiagramNamesFourStates()
    {
        var text = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), "CLAUDE.md"), System.Text.Encoding.UTF8);
        Assert.Contains("\u6d88\u5316\u8d26\u76ee\u00b7\u56db\u6001\u89c1\u4e0b", text, StringComparison.Ordinal);
    }

    [Fact]
    public void PrToolDocumentationNoLongerRequiresCallerPolling()
    {
        var text = File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "CLAUDE.md"), Encoding.UTF8);
        Assert.Contains("`pr.sh` 为 `open`/`watch` 双动词", text, StringComparison.Ordinal);
        Assert.Contains("缺省不 arm auto-merge", text, StringComparison.Ordinal);
        Assert.DoesNotContain("`make pr-open` 自带 auto-merge", text, StringComparison.Ordinal);
        Assert.DoesNotContain("create → App-token 隔离 → arm auto-merge → 等 required-CI 判词", text, StringComparison.Ordinal);
        Assert.DoesNotContain("需要重复由调用方 shell 循环", text, StringComparison.Ordinal);
        Assert.DoesNotContain("单动词(`update`", text, StringComparison.Ordinal);
    }
}
