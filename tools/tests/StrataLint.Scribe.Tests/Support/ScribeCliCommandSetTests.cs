using StrataLint.Scribe;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeCliCommandSetTests
{
    // 孪生断言:StrataLint.Tests 的 CliVerbLinkageTests 以本地常量表钉 Scribe 动词集
    // (它不得引用本程序集,依赖方向 Tests→Cli+Engine)。此处钉真源与该表一致;
    // 新增/删除 Scribe 动词时两侧必有一红,防表漂移成孤立手抄。
    [Fact]
    public void ImplementedCommandsMatchTheLinkagePinnedSet()
    {
        var pinned = new[]
        {
            "describe-report", "emit", "emit-values", "filemap", "markdown-check", "projections",
        };

        Assert.Equal(
            pinned.OrderBy(static v => v, StringComparer.Ordinal),
            ScribeCli.ImplementedCommands.OrderBy(static v => v, StringComparer.Ordinal));
    }
}
