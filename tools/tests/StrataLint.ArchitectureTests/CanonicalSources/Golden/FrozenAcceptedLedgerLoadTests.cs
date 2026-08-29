using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

/// <summary>
/// 冻结账本 v5 迁移期,`Golden/Frozen/accepted/` 同时含 v5 与尚未被重写的 legacy 分片
/// (expand–migrate–contract 的 expand 期)。本测试判**仓库里实际那一份**能否整体读出。
///
/// **为什么住在 ArchitectureTests 而不是 StrataLint.Tests**:它要读整个 accepted 面。
/// 目录枚举(`Directory.EnumerateFiles`)被 `ScribeTestMapDeriver` 记为
/// `TestMapUnknownReason.DirectoryEnumeration` ⟹ 新增即被 SL-003 以
/// `AdmissionEffect.Block` 拦下(2026-08-29 实测,PR #3884 第四轮)。
/// 声明式枚举 `EnumerateDeclared(root, "<字面量前缀>")` 读 git index 而非目录,
/// 不记该 reason,**且**把前缀登记为 declared input —— 于是只改该前缀下分片的 PR
/// 会选中本测试。那个 accessor 只在本项目内,故测试随它走。
///
/// **本测试不断言 schema 版本的分布。** 语料是 append-only 且由 writer 持续推进的,
/// 「存在一条 v4」这类断言会在 contract 步把 legacy 清零的那一刻把每个 PR 都判红
/// (本仓已记的「append-only 语料不可钉分布」)。逐版本的解码正确性由
/// `FrozenLedgerTransitionTests` 的合成夹具承担,那里版本是输入而非观测。
/// </summary>
public sealed class FrozenAcceptedLedgerLoadTests
{
    [Fact]
    public void EveryTrackedAcceptedEventLoadsThroughTheTrustedLoader()
    {
        var repositoryRoot = RepositoryLayout.FindRoot();
        var files = GitIndexRepositoryFiles
            .EnumerateDeclared(repositoryRoot, "Golden/Frozen/accepted")
            .Where(static file => file.RelativePath.EndsWith(".json", StringComparison.Ordinal))
            .OrderBy(static file => file.RelativePath, StringComparer.Ordinal)
            .Select(static file =>
            {
                var bytes = File.ReadAllBytes(file.FullPath);
                return new RepositoryFile(
                    RepoPath.CreateKnown(file.RelativePath),
                    ImmutableArray.CreateRange(bytes),
                    Encoding.UTF8.GetString(bytes));
            })
            .ToImmutableArray();

        // 放行侧守卫:枚举若因前缀写错而返回空,下面两条断言都会恒真。
        Assert.NotEmpty(files);

        var loaded = Assert.IsType<DagLedgerFilesLoadOutcome.Loaded>(
            FrozenAcceptedEventLoader.LoadTrustedFiles(files));

        Assert.Equal(files.Length, loaded.Events.Length);
    }
}
