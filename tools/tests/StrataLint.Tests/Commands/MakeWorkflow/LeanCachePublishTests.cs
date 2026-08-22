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
    /// tag 必须把身份三元组（toolchain、config、sources）全部绑进去。少任何一个，两棵语义不同的树就会共用一个 tag，
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
        // 反向钉住：tag 不得重新引入平台维度。加回去会把主检出（darwin-arm64）
        // 挡在 CI 产物（linux-aarch64）之外，而 olean 实测不含平台相关二进制
        // （*.o/*.so/*.dylib/*.a/*.dll 全为 0），mathlib 亦对所有平台发同一份缓存。
        Assert.DoesNotContain("${os}", tag, StringComparison.Ordinal);
        Assert.DoesNotContain("${arch}", tag, StringComparison.Ordinal);
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
    /// 取回路径的每一种**不匹配**都必须走向 `miss` 且退出非零。
    /// 「安静地用一份旧的或不匹配的归档」是这条路径唯一真正危险的失败模式。
    /// 「精确地址不存在」已不在此列:dev 约 16 提交/小时而发布一轮 6.5 分钟起,
    /// `sources_sha256` **结构性**追不上(实测:建 worktree 到 fetch 之间 dev 就前进了)。
    /// 那时回退到同 `config` 的最近一份,差量交给 `lake build` —— 且**并不安静**:
    /// 输出 `"mode":"prefix"` 与实际取到的 `resolved` tag。见 ConsumerFallsBackWithinTheSameConfig。
    /// </summary>
    [Theory]
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
    /// 精确地址取不到时必须回退到**同 config** 的最近一份,而不是放弃。
    /// 这一条与上面那条 fail-closed 清单是配对的:从清单里移走「无精确地址」
    /// 只有在这里补上「那时它必须回退」才不留缺口 —— 否则删掉一条断言就等于
    /// 把契约一起丢掉,而没有任何东西会红。
    /// </summary>
    [Fact]
    public void ConsumerFallsBackWithinTheSameConfig()
    {
        var script = Script();
        // 回退的检索键必须绑 toolchain 与 config，且只放宽 sources。
        Assert.Contains("prefix=\"lean-cache-v1-${slug}-${config_sha256:0:16}-\"",
            script, StringComparison.Ordinal);
        // 回退必须可辨识:不得安静地用一份旧归档。
        Assert.Contains("\"mode\":\"%s\"", script, StringComparison.Ordinal);
        Assert.Contains("\"resolved\":\"%s\"", script, StringComparison.Ordinal);
        // 连前缀都无命中时仍 fail-closed。
        Assert.Contains("no release for this address nor its config prefix",
            script, StringComparison.Ordinal);
    }

    /// <summary>
    /// **依赖层身份**必须逐字段比对。只验摘要不够:一份**完好无损**但产自另一个
    /// toolchain 的归档，其摘要照样对得上。
    /// 身份 = `toolchain` + `config_sha256`。`os`/`arch` 不在其中(olean 无平台相关
    /// 二进制:`*.o/*.so/*.dylib/*.a/*.dll` 皆 0;mathlib 亦对所有平台发同一份);
    /// `sources_sha256` 是**新旧**不是身份,由前缀回退处理。
    /// </summary>
    [Fact]
    public void ConsumerComparesEveryIdentityFieldNotJustTheDigest()
    {
        var script = Script();
        var loop = Assert.Single(
            script.Split('\n'),
            static line => line.Contains("for field in", StringComparison.Ordinal));

        foreach (var field in new[] { "toolchain", "config_sha256" })
        {
            Assert.Contains(field, loop, StringComparison.Ordinal);
        }

        // 反向钉住:不得把不承重的维度加回这道门。
        // `os`/`arch` —— olean 里没有平台相关二进制(`*.o/*.so/*.dylib/*.a/*.dll` 皆 0,
        //   `file(1)` 判 olean 为 data),mathlib 亦对所有平台发同一份缓存;
        //   加回去会把主检出(darwin-arm64)挡在 CI 产物(linux-aarch64)之外,
        //   而端到端实测正是跨平台消费成功:replayed=680 built=0。
        // `sources_sha256` —— 它是新旧不是身份;要求它相等即要求精确命中,
        //   而 dev 约 16 提交/小时,精确命中结构性不可达。
        foreach (var field in new[] { "os", "arch", "sources_sha256" })
        {
            Assert.DoesNotContain(field, loop, StringComparison.Ordinal);
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
