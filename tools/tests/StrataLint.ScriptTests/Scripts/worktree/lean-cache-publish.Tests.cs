using System.Text;
using StrataLint.Engine;

namespace StrataLint.ScriptTests;

/// <summary>
/// `lean-cache-publish.sh` 发布并取回 Lean 构建缓存。那个归档是**加速器**，不是权威：
/// 它不构成独立的 admission 证据。这里钉住的是身份绑定，以及消费侧对每一种不匹配都
/// fail-closed。
///
/// 此处曾写「它永远不进 admission 信任链」，那句话是假的：归档的 .olean 会被 Lake 当作
/// 构建输入复用，canonical 报告又从那个环境读声明，故发布者位于 admission 下方。理由与
/// 替代不变量见脚本头的勘误段（#2729 三席判决）。**这些断言本身不受影响**——它们钉的是
/// tag 身份与 fail-closed，从来不是那句信任链声明。
/// </summary>
[ScriptSubject("tools/scripts/worktree/lean-cache-publish.sh")]
public sealed class LeanCachePublishTests
{
    private static string Script() => TestRepositoryLayout.ReadAllText(
        RepositoryRelativePath.Create("tools/scripts/worktree/lean-cache-publish.sh"));

    /// <summary>
    /// 发布者身份。归档的触发集合自 #2818 起只有 `schedule`，即唯一合法发布者是 dev 上的
    /// 定时 CI producer；consumer 侧要靠这两个值把资产绑回那次运行。缺失即拒绝发布——
    /// 发不出资产，好过发一个事后无法归属的资产。这里真跑脚本，不只读文本：一条断言
    /// 只证明字符串在，不证明它会执行。
    /// </summary>
    [Fact]
    public void PublishRefusesWithoutAnAttributableProducerIdentity()
    {
        var script = ScriptPath();

        var missing = RunPublish(script, sha: null, runId: null);
        Assert.NotEqual(0, missing.ExitCode);
        Assert.Contains(
            "refusing to publish an unattributable archive",
            missing.Text,
            StringComparison.Ordinal);

        var malformed = RunPublish(script, sha: "nothex", runId: "42");
        Assert.NotEqual(0, malformed.ExitCode);
        Assert.Contains(
            "refusing to publish an unattributable archive",
            malformed.Text,
            StringComparison.Ordinal);

        var noRunId = RunPublish(script, sha: new string('a', 40), runId: null);
        Assert.NotEqual(0, noRunId.ExitCode);
        Assert.Contains("GITHUB_RUN_ID", noRunId.Text, StringComparison.Ordinal);
    }

    /// <summary>
    /// 放行侧的阳性对照，端到端。**只断言「输出里没有拒绝消息」是不够的** —— 一个
    /// 校验完身份就什么都不做的脚本同样能通过那种断言。这里用假的 `gh`/`lake` 走完整条
    /// 发布路径，然后检查 `gh release create` **实际收到了什么**：tag 必须建在本次的
    /// producer commit 上，manifest 必须带上产地两项。
    /// </summary>
    [Fact]
    public void PublishAnchorsTheTagToTheProducerCommitAndRecordsItInTheManifest()
    {
        const string Sha = "0123456789abcdef0123456789abcdef01234567";
        using var fixture = new PublishFixture();

        var result = fixture.RunPublish(ScriptPath(), Sha, "4242");

        Assert.Equal(0, result.ExitCode);

        // gh 实际收到的参数：tag 的锚必须是本次 producer commit，而不是 gh 执行那一刻
        // 默认分支的 tip。
        var arguments = fixture.RecordedGhArguments();
        var target = Array.IndexOf(arguments, "--target");
        Assert.True(target >= 0, $"gh release create carried no --target: {string.Join(' ', arguments)}");
        Assert.Equal(Sha, arguments[target + 1]);

        // manifest 是 consumer 侧唯一能据以核验产地的东西；写不出这两项，后续核验无从谈起。
        var manifest = fixture.CapturedManifest();
        Assert.Contains($"producer_commit_sha={Sha}", manifest, StringComparison.Ordinal);
        Assert.Contains("workflow_run_id=4242", manifest, StringComparison.Ordinal);
    }

    /// <summary>
    /// Darwin's system `shasum` is a Perl program. The fixture models its exit-9 startup failure
    /// for an unavailable caller locale, including on hosts that now provide C.UTF-8.
    /// </summary>
    [Fact]
    public void PublishPinsAPortableLocaleAndWritesTheCorrectArchiveDigest()
    {
        const string Sha = "0123456789abcdef0123456789abcdef01234567";
        using var fixture = new PublishFixture(requirePortableLocaleForShasum: true);

        var result = fixture.RunPublish(ScriptPath(), Sha, "4242", callerLocale: "C.UTF-8");

        Assert.Equal(0, result.ExitCode);
        var expected = Convert.ToHexStringLower(
            System.Security.Cryptography.SHA256.HashData(Encoding.UTF8.GetBytes("archive\n")));
        Assert.Contains($"archive_sha256={expected}", fixture.CapturedManifest(), StringComparison.Ordinal);
    }

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

    private static string ScriptPath() => Path.Combine(
        TestRepositoryLayout.FindRoot(),
        "tools",
        "scripts",
        "worktree",
        "lean-cache-publish.sh");

    private static PublishAttempt RunPublish(string script, string? sha, string? runId)
    {
        // `env` 既能设也能删：删掉才测得到「变量根本不存在」那一支，设成空串是另一回事。
        // 所有 `-u` 必须排在赋值之前 —— env 一旦读到 NAME=VALUE，后面的参数就按命令解析，
        // 于是 `-u` 会被当成可执行文件名（实测 "env: -u: No such file or directory"）。
        var unset = new List<string>();
        var assign = new List<string>();
        if (sha is null) unset.AddRange(["-u", "GITHUB_SHA"]);
        else assign.Add($"GITHUB_SHA={sha}");
        if (runId is null) unset.AddRange(["-u", "GITHUB_RUN_ID"]);
        else assign.Add($"GITHUB_RUN_ID={runId}");
        var environment = new List<string>([.. unset, .. assign]);

        var result = TestProcessRunner.Run(
            "/usr/bin/env",
            [.. environment, "/bin/bash", script, "publish"],
            Path.GetDirectoryName(script)!,
            TestBudgets.WorkflowProcessHangGuard,
            256 * 1024);

        return new PublishAttempt(
            result.ExitCode,
            Encoding.UTF8.GetString(result.StandardOutput)
                + Encoding.UTF8.GetString(result.StandardError));
    }

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
                + $"  printf '%s\\n' '{NewTag}' '{SupersededA}' '{SupersededB}' '{OtherConfig}'\n"
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
        Assert.Contains(SupersededA, removed);
        Assert.Contains(SupersededB, removed);

        // ② 刚建的那份绝不被删 —— 删了它就是把一次浪费换成一次断供。
        Assert.DoesNotContain(NewTag, removed);

        // ③ 别的 config 的份绝不被删 —— 它服务的是另一条 pin，与本次无关。
        Assert.DoesNotContain(OtherConfig, removed);

        // 收据必须报出删了几份；剪枝静默就等于没有账。
        Assert.Contains("\"pruned\":2", result.Text, StringComparison.Ordinal);
    }

    private sealed record PublishAttempt(int ExitCode, string Text);

    /// <summary>
    /// 解包必须只有一个入口，且它在产地核验之后。
    ///
    /// 逐条枚举控制流会漏 —— 漏掉的那条恰恰是将来新加的那条。这里改成**结构断言**：
    /// 脚本中 `lake unpack` 恰好出现一次，且落在 `consume_verified_archive` 函数体内，
    /// 而该函数的定义位置在核验段之后。任何绕开核验去解包的新分支都会先让这条红。
    /// </summary>
    [Fact]
    public void VerifiedConsumptionHasASingleEntryPoint()
    {
        var script = Script();
        var lines = script.Split('\n');

        // 只数真正的命令行。注释里提到 `lake unpack`（包括解释这条断言本身的那段）
        // 不是调用点；把注释算进来会让判据把自己也数一遍 —— 实测第一版正是如此，
        // 数出 2 处，其中一处是本测试的说明文字。
        var unpackLines = lines
            .Select(static (text, index) => (text, index))
            .Where(static line => line.text.Contains("lake unpack", StringComparison.Ordinal)
                && !line.text.TrimStart().StartsWith('#'))
            .ToArray();
        var unpack = Assert.Single(unpackLines);

        var definition = Array.FindIndex(
            lines,
            static line => line.TrimStart().StartsWith("consume_verified_archive()", StringComparison.Ordinal));
        Assert.True(definition >= 0, "consume_verified_archive is not defined");

        var provenanceGate = Array.FindIndex(
            lines,
            static line => line.Contains("fail_provenance()", StringComparison.Ordinal));
        Assert.True(provenanceGate >= 0, "the provenance gate is not defined");

        Assert.True(
            provenanceGate < definition,
            "the unpack entry point must be defined after the provenance gate");
        Assert.True(
            unpack.index > definition,
            "the only lake unpack must sit inside consume_verified_archive");
    }

    /// <summary>
    /// 消费侧产地核验的 fail-closed 矩阵。摘要与依赖层身份只证明「字节没坏、层对得上」，
    /// 不证明**是谁产的** —— manifest 与 payload 同处一个发布面，有写权者可一并替换而保持
    /// 自洽。故每一项产地不符都必须判 rejected 且**不解包**。
    ///
    /// 每一行都是一个**单点偏离**：其余全部合规，只坏一处。这样红了才说明是那一处被检出，
    /// 而不是被别的检查顺带拦下。
    /// </summary>
    [Theory]
    [InlineData("no-producer", "manifest carries no producer commit")]
    [InlineData("no-run-id", "manifest carries no workflow run id")]
    [InlineData("wrong-author", "release author is")]
    [InlineData("wrong-target", "does not match the declared producer commit")]
    [InlineData("wrong-uploader", "an asset was uploaded by")]
    [InlineData("wrong-workflow", "workflow_id is")]
    [InlineData("wrong-event", "event is")]
    [InlineData("wrong-branch", "head_branch is")]
    [InlineData("wrong-head-sha", "head_sha is")]
    [InlineData("failed-run", "conclusion is")]
    [InlineData("wrong-archive-digest", "do not match the digest GitHub recorded")]
    [InlineData("extra-asset", "assets, expected exactly 2")]
    public void FetchRejectsEveryProvenanceDeviation(string deviation, string expected)
    {
        using var fixture = new FetchFixture(deviation);

        var result = fixture.RunFetch(ScriptPath());

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("\"status\":\"rejected\"", result.Text, StringComparison.Ordinal);
        Assert.Contains("\"stage\":\"provenance\"", result.Text, StringComparison.Ordinal);
        Assert.Contains(expected, result.Text, StringComparison.Ordinal);
        Assert.False(fixture.Unpacked, "a rejected archive must never be unpacked");
    }

    /// <summary>
    /// 放行侧。上面十行只钉拒绝；一个「什么都拒绝」的核验同样能通过它们。产地齐备时必须
    /// **解包**，并把产地写进收据 —— 收据是下游唯一能据以复算的东西。
    /// </summary>
    [Fact]
    public void FetchAcceptsAndRecordsAFullyAttributedArchive()
    {
        using var fixture = new FetchFixture(deviation: null);

        var result = fixture.RunFetch(ScriptPath());

        Assert.Equal(0, result.ExitCode);
        Assert.True(fixture.Unpacked, "a fully attributed archive must be unpacked");
        Assert.Contains("\"status\":\"unpacked\"", result.Text, StringComparison.Ordinal);
        Assert.Contains($"\"producer_commit_sha\":\"{FetchFixture.ProducerSha}\"", result.Text, StringComparison.Ordinal);
        Assert.Contains("\"workflow_run_id\":\"7777\"", result.Text, StringComparison.Ordinal);
    }

    /// <summary>
    /// 一棵最小的可发布树，外加 PATH 上的假 `gh`/`lake`。夹具存在的理由是上面那条断言：
    /// 要判「发布确实按 producer commit 锚定」，就得看 gh **实际收到**的参数，而不是脚本
    /// 里有没有那个字符串。
    /// </summary>
    private sealed class PublishFixture : IDisposable
    {
        private readonly TemporaryDirectory root = new();

        internal PublishFixture(bool requirePortableLocaleForShasum = false)
        {
            Repository = Path.Combine(root.Path, "repo");
            Bin = Path.Combine(root.Path, "bin");
            GhArgumentsPath = Path.Combine(root.Path, "gh-arguments.txt");
            ManifestPath = Path.Combine(root.Path, "captured-manifest.txt");

            Directory.CreateDirectory(Path.Combine(Repository, ".lake", "build"));
            File.WriteAllText(
                Path.Combine(Repository, ".lake", "build", "placeholder"),
                "content layer\n");
            File.WriteAllText(
                Path.Combine(Repository, "lean-toolchain"),
                "leanprover/lean4:v4.31.0\n");

            var helper = Path.Combine(Repository, "tools", "scripts", "report", "lean-report-input.sh");
            Directory.CreateDirectory(Path.GetDirectoryName(helper)!);
            WriteExecutable(
                helper,
                "#!/usr/bin/env bash\nprintf 'addr producer %s %s\\n' "
                    + $"\"{new string('1', 64)}\" \"{new string('2', 64)}\"\n");

            Directory.CreateDirectory(Bin);
            // release view 报「不存在」，脚本才会走到创建；create 把参数与 manifest 留证。
            WriteExecutable(
                Path.Combine(Bin, "gh"),
                "#!/usr/bin/env bash\n"
                    + "if [[ \"$1\" == 'release' && \"$2\" == 'view' ]]; then exit 1; fi\n"
                    + "if [[ \"$1\" == 'release' && \"$2\" == 'create' ]]; then\n"
                    + $"  printf '%s\\n' \"$@\" > '{GhArgumentsPath}'\n"
                    + "  for argument in \"$@\"; do\n"
                    + $"    case \"$argument\" in *manifest.txt) cp \"$argument\" '{ManifestPath}' ;; esac\n"
                    + "  done\n"
                    + "  exit 0\n"
                    + "fi\n"
                    + "exit 0\n");
            WriteExecutable(
                Path.Combine(Bin, "lake"),
                "#!/usr/bin/env bash\n"
                    + "if [[ \"$1\" == 'pack' ]]; then printf 'archive\\n' > \"$2\"; fi\n"
                    + "exit 0\n");
            if (requirePortableLocaleForShasum)
            {
                WriteExecutable(
                    Path.Combine(Bin, "shasum"),
                    "#!/usr/bin/env bash\n"
                        + "if [[ \"${LC_ALL:-}\" != 'C' ]]; then\n"
                        + "  printf 'shasum: locale startup failed for LC_ALL=%s\\n' \"${LC_ALL:-<unset>}\" >&2\n"
                        + "  exit 9\n"
                        + "fi\n"
                        + "exec /usr/bin/shasum \"$@\"\n");
            }
        }

        private string Repository { get; }

        internal string Bin { get; }

        private string GhArgumentsPath { get; }

        private string ManifestPath { get; }

        internal PublishAttempt RunPublish(
            string script,
            string sha,
            string runId,
            string? callerLocale = null)
        {
            var arguments = new List<string>
            {
                $"PATH={Bin}:{Environment.GetEnvironmentVariable("PATH")}",
                $"GITHUB_SHA={sha}",
                $"GITHUB_RUN_ID={runId}",
            };
            if (callerLocale is not null)
            {
                arguments.Add($"LC_ALL={callerLocale}");
                arguments.Add($"LANG={callerLocale}");
            }
            arguments.AddRange(
            [
                "/bin/bash",
                script,
                "publish",
                "--repository",
                Repository,
            ]);

            var result = TestProcessRunner.Run(
                "/usr/bin/env",
                [.. arguments],
                Repository,
                TestBudgets.WorkflowProcessHangGuard,
                256 * 1024);

            return new PublishAttempt(
                result.ExitCode,
                Encoding.UTF8.GetString(result.StandardOutput)
                    + Encoding.UTF8.GetString(result.StandardError));
        }

        internal string[] RecordedGhArguments() => File.Exists(GhArgumentsPath)
            ? File.ReadAllLines(GhArgumentsPath)
            : [];

        internal string CapturedManifest() =>
            File.Exists(ManifestPath) ? File.ReadAllText(ManifestPath) : string.Empty;

        public void Dispose() => root.Dispose();

        private static void WriteExecutable(string path, string contents)
        {
            File.WriteAllText(path, contents);
            // 走 chmod 而不是 File.SetUnixFileMode：后者带 CA1416（Windows 不支持），
            // 在 warnaserror 下即编译失败。ReportSupervisorFixture 已是这个写法。
            var chmod = TestProcessRunner.Run(
                "chmod",
                ["+x", path],
                Path.GetDirectoryName(path)!,
                BoundedProcessRunner.HangDetectionBudget,
                4096);
            Assert.Equal(0, chmod.ExitCode);
        }
    }

    /// <summary>
    /// 一棵最小的可消费树，外加 PATH 上的假 `gh`/`lake`/`jq`(用真 jq)。构造参数 `deviation`
    /// 恰好改一处,其余保持合规 —— 判据要能指认是哪一处被检出。
    /// </summary>
    private sealed class FetchFixture : IDisposable
    {
        internal const string ProducerSha = "89abcdef0123456789abcdef0123456789abcdef";

        private readonly TemporaryDirectory root = new();

        internal FetchFixture(string? deviation)
        {
            Repository = Path.Combine(root.Path, "repo");
            Bin = Path.Combine(root.Path, "bin");
            UnpackMarker = Path.Combine(root.Path, "unpacked.marker");

            Directory.CreateDirectory(Repository);
            File.WriteAllText(
                Path.Combine(Repository, "lean-toolchain"),
                "leanprover/lean4:v4.31.0\n");
            var helper = Path.Combine(Repository, "tools", "scripts", "report", "lean-report-input.sh");
            Directory.CreateDirectory(Path.GetDirectoryName(helper)!);
            WriteExecutable(
                helper,
                "#!/usr/bin/env bash\nprintf 'addr producer %s %s\\n' "
                    + $"\"{new string('3', 64)}\" \"{new string('4', 64)}\"\n");

            var producer = deviation == "no-producer" ? "" : $"producer_commit_sha={ProducerSha}\n";
            var runId = deviation == "no-run-id" ? "" : "workflow_run_id=7777\n";
            var author = deviation == "wrong-author" ? "someone" : "github-actions[bot]";
            var target = deviation == "wrong-target" ? "dev" : ProducerSha;
            var uploader = deviation == "wrong-uploader" ? "someone" : "github-actions[bot]";
            var workflowId = deviation == "wrong-workflow" ? "999" : "42";
            var runEvent = deviation == "wrong-event" ? "workflow_dispatch" : "schedule";
            var branch = deviation == "wrong-branch" ? "harness/x" : "dev";
            var headSha = deviation == "wrong-head-sha" ? new string('b', 40) : ProducerSha;
            var conclusion = deviation == "failed-run" ? "failure" : "success";

            var payload = Path.Combine(root.Path, "payload");
            Directory.CreateDirectory(payload);
            File.WriteAllText(Path.Combine(payload, "lean-build.tgz"), "archive bytes\n");
            var digest = Convert.ToHexStringLower(
                System.Security.Cryptography.SHA256.HashData(
                    File.ReadAllBytes(Path.Combine(payload, "lean-build.tgz"))));
            File.WriteAllText(
                Path.Combine(payload, "manifest.txt"),
                $"toolchain=leanprover/lean4:v4.31.0\nconfig_sha256={new string('4', 64)}\n"
                    + $"sources_sha256={new string('3', 64)}\narchive_sha256={digest}\n"
                    + $"archive_bytes=14\n{producer}{runId}");

            var archiveDigest = deviation == "wrong-archive-digest"
                ? new string('c', 64)
                : digest;

            Directory.CreateDirectory(Bin);
            // 严格夹具：只认下面这三个端点的**完整**形状，其余一律非零退出。
            // 宽匹配（`*/releases/tags/*` 一类）会让脚本调错端点也照样绿，那样测的
            // 就不是脚本的行为，而是夹具的宽容度。
            WriteExecutable(
                Path.Combine(Bin, "gh"),
                "#!/usr/bin/env bash\n"
                    + "if [[ \"$1\" == 'release' && \"$2\" == 'download' ]]; then\n"
                    + "  destination=''\n"
                    + "  saw_repo=0; saw_archive=0; saw_manifest=0\n"
                    + "  while [[ $# -gt 0 ]]; do\n"
                    + "    case \"$1\" in\n"
                    + "      --dir) destination=\"$2\" ;;\n"
                    + "      --repo) saw_repo=1 ;;\n"
                    + "      lean-build.tgz) saw_archive=1 ;;\n"
                    + "      manifest.txt) saw_manifest=1 ;;\n"
                    + "    esac\n"
                    + "    shift\n"
                    + "  done\n"
                    + "  [[ -n \"$destination\" && $saw_repo == 1 && $saw_archive == 1 && $saw_manifest == 1 ]] || exit 1\n"
                    + $"  cp '{payload}'/* \"$destination\"\n"
                    + "  exit 0\n"
                    + "fi\n"
                    + "if [[ \"$1\" == 'api' ]]; then\n"
                    + "  case \"$2\" in\n"
                    + "    repos/*/releases/tags/*)\n"
                    + $"      printf '{{\"author\":{{\"login\":\"{author}\"}},\"target_commitish\":\"{target}\",\"assets\":["
                    + $"{{\"name\":\"lean-build.tgz\",\"digest\":\"sha256:{archiveDigest}\",\"uploader\":{{\"login\":\"github-actions[bot]\"}}}},"
                    // 错误 uploader 刻意放在**第二个**资产上：第一个保持正确，才抓得住
                    // 「只查第一个就返回」这类实现。放在第一个的话，那种实现照样红，
                    // 用例就分辨不出两者。
                    + $"{{\"name\":\"manifest.txt\",\"digest\":\"sha256:{new string('e', 64)}\",\"uploader\":{{\"login\":\"{uploader}\"}}}}"
                    + (deviation == "extra-asset"
                        ? ",{\"name\":\"notes.txt\",\"digest\":\"sha256:"
                            + new string('f', 64)
                            + "\",\"uploader\":{\"login\":\"github-actions[bot]\"}}"
                        : string.Empty)
                    + "]}\\n' ;;\n"
                    + "    repos/*/actions/workflows/lean-cache-publish.yml)\n"
                    + "      [[ \"$3\" == '--jq' && \"$4\" == '.id' ]] || exit 1\n"
                    + "      printf '42\\n' ;;\n"
                    + "    repos/*/actions/runs/7777)\n"
                    + $"      printf '{{\"workflow_id\":{workflowId},\"event\":\"{runEvent}\",\"head_branch\":\"{branch}\",\"head_sha\":\"{headSha}\",\"conclusion\":\"{conclusion}\"}}\\n' ;;\n"
                    + "    *) exit 1 ;;\n"
                    + "  esac\n"
                    + "  exit 0\n"
                    + "fi\n"
                    + "exit 1\n");
            WriteExecutable(
                Path.Combine(Bin, "lake"),
                "#!/usr/bin/env bash\n"
                    + $"if [[ \"$1\" == 'unpack' ]]; then printf 'yes\\n' > '{UnpackMarker}'; fi\n"
                    + "exit 0\n");
        }

        private string Repository { get; }

        private string Bin { get; }

        private string UnpackMarker { get; }

        internal bool Unpacked => File.Exists(UnpackMarker);

        internal PublishAttempt RunFetch(string script)
        {
            var result = TestProcessRunner.Run(
                "/usr/bin/env",
                [
                    $"PATH={Bin}:{Environment.GetEnvironmentVariable("PATH")}",
                    "/bin/bash",
                    script,
                    "fetch",
                    "--repository",
                    Repository,
                ],
                Repository,
                TestBudgets.WorkflowProcessHangGuard,
                256 * 1024);

            return new PublishAttempt(
                result.ExitCode,
                Encoding.UTF8.GetString(result.StandardOutput)
                    + Encoding.UTF8.GetString(result.StandardError));
        }

        public void Dispose() => root.Dispose();

        private static void WriteExecutable(string path, string contents)
        {
            File.WriteAllText(path, contents);
            var chmod = TestProcessRunner.Run(
                "chmod",
                ["+x", path],
                Path.GetDirectoryName(path)!,
                BoundedProcessRunner.HangDetectionBudget,
                4096);
            Assert.Equal(0, chmod.ExitCode);
        }
    }
}
