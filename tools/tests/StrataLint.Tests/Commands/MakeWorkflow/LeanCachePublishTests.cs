namespace StrataLint.Tests;

/// <summary>
/// `lean-cache-publish.sh` 发布并取回 Lean 构建缓存。那个归档是**加速器**，不是权威：
/// 它永远不进 admission 信任链，它的存在也永远不能让任何判词从红变绿。
/// 这里钉住的正是那条边界，以及消费侧对每一种不匹配都 fail-closed。
/// </summary>
public sealed class LeanCachePublishTests
{
    private static string Script() => TestRepositoryLayout.ReadAllText(
        RepositoryRelativePath.Create("tools/scripts/worktree/lean-cache-publish.sh"));

    /// <summary>
    /// tag 必须把身份五元组全部绑进去。少任何一个，两棵语义不同的树就会共用一个 tag，
    /// 而它们的归档互相覆盖时没有任何东西会红。
    /// </summary>
    [Fact]
    public void CacheTagBindsToolchainPlatformAndBothContentAddresses()
    {
        var script = Script();
        var tag = Assert.Single(
            script.Split('\n'),
            static line => line.TrimStart().StartsWith("tag=", StringComparison.Ordinal));

        Assert.Contains("${slug}", tag, StringComparison.Ordinal);
        Assert.Contains("${os}", tag, StringComparison.Ordinal);
        Assert.Contains("${arch}", tag, StringComparison.Ordinal);
        Assert.Contains("${config_sha256:", tag, StringComparison.Ordinal);
        Assert.Contains("${sources_sha256:", tag, StringComparison.Ordinal);
    }

    /// <summary>
    /// 缓存 tag 与 spec A14 的 `E&lt;n&gt;` 发布 tag 必须分属不同命名空间：
    /// 前者是可丢弃的构建产物，后者承担发布语义。共用一个空间会让「删掉陈旧缓存」
    /// 变成一个可能删掉版本发布的操作。
    /// </summary>
    [Fact]
    public void CacheTagsUseANamespaceSeparateFromReleaseTags()
    {
        var script = Script();
        Assert.Contains("lean-cache-v1-", script, StringComparison.Ordinal);
        Assert.DoesNotContain("tag=\"E", script, StringComparison.Ordinal);
        Assert.DoesNotContain("tag=E", script, StringComparison.Ordinal);
    }

    /// <summary>
    /// 两个内容地址必须取自本仓既有的唯一真源，不得在此另算一套。
    /// 第二套哈希实现会与第一套悄悄分叉，而分叉本身不产生任何症状。
    /// </summary>
    [Fact]
    public void AddressesComeFromTheExistingInputHelperRatherThanASecondImplementation()
    {
        var script = Script();
        Assert.Contains("lean-report-input.sh", script, StringComparison.Ordinal);
        Assert.Contains("address --repository", script, StringComparison.Ordinal);
        Assert.DoesNotContain("sha256sum <<<", script, StringComparison.Ordinal);
    }

    /// <summary>
    /// 取回路径的每一种不匹配都必须走向 `miss` 且退出非零。
    /// 「安静地用一份旧的或不匹配的归档」是这条路径唯一真正危险的失败模式。
    /// </summary>
    [Theory]
    [InlineData("no release for this exact address")]
    [InlineData("release is missing the archive or its manifest")]
    [InlineData("manifest declares no digest")]
    [InlineData("digest mismatch")]
    public void EveryConsumerMismatchFailsClosed(string reason)
    {
        var script = Script();
        Assert.Contains(reason, script, StringComparison.Ordinal);

        var line = Assert.Single(
            script.Split('\n'),
            l => l.Contains(reason, StringComparison.Ordinal));
        Assert.Contains("\"status\":\"miss\"", line, StringComparison.Ordinal);
        Assert.Contains("exit 1", line, StringComparison.Ordinal);
    }

    /// <summary>
    /// 五元组里的每一个字段都必须被逐字段比对。只验摘要是不够的：
    /// 一份**完好无损**但产自另一个 toolchain 或另一个平台的归档，其摘要照样对得上。
    /// </summary>
    [Fact]
    public void ConsumerComparesEveryIdentityFieldNotJustTheDigest()
    {
        var script = Script();
        var loop = Assert.Single(
            script.Split('\n'),
            static line => line.Contains("for field in", StringComparison.Ordinal));

        foreach (var field in new[] { "toolchain", "os", "arch", "config_sha256", "sources_sha256" })
        {
            Assert.Contains(field, loop, StringComparison.Ordinal);
        }
        Assert.Contains("mismatch", script, StringComparison.Ordinal);
    }

    /// <summary>
    /// 发布是幂等的：同一个内容地址只发一次。少了这条，重复发布会拿新字节覆盖
    /// 一个本应不可变的 tag，于是「同一地址永远对应同一份字节」这个前提就没了。
    /// </summary>
    [Fact]
    public void PublishingAnAddressThatAlreadyExistsIsANoOp()
    {
        var script = Script();
        Assert.Contains("gh release view", script, StringComparison.Ordinal);
        var guard = Assert.Single(
            script.Split('\n'),
            static line => line.Contains("\"status\":\"exists\"", StringComparison.Ordinal));
        Assert.Contains("tag", guard, StringComparison.Ordinal);
    }

    /// <summary>
    /// 这个归档不是权威。脚本自己必须把这一点写下来——不是为了好看，而是因为
    /// 下一个读它的人得知道：把它接进 admission 是越界，不是优化。
    /// </summary>
    [Fact]
    public void ScriptStatesThatTheArchiveIsNeverAdmissionEvidence()
    {
        var script = Script();
        Assert.Contains("admission", script, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("accelerator", script, StringComparison.OrdinalIgnoreCase);
    }

    /// <summary>
    /// `make` 的两个入口必须委托给 canonical 实现，而不是复制它的逻辑（器律①：层内只委托）。
    /// </summary>
    [Fact]
    public void MakeTargetsDelegateToTheCanonicalScript()
    {
        var makefile = TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create("Makefile"));
        foreach (var verb in new[] { "publish", "fetch" })
        {
            var recipe = Assert.Single(
                makefile.Split('\n'),
                line => line.Contains("lean-cache-publish.sh " + verb, StringComparison.Ordinal));
            Assert.StartsWith("\t", recipe, StringComparison.Ordinal);
        }
    }
}
