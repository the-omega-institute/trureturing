using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

/// <summary>
/// 隔离的类型化阻断分类(#2137)。此前 <c>quarantine</c> 只有两个自由文本字段,故
/// 「某原子为何不该被再次提供」不可机器判、不可分类统计——而生产线实测已产出 21 条
/// **已分类**的弹出行(2 already-covered / 7 missing-prerequisite / 12 multi-clause-guard),
/// 那三类即本字段的封闭字母表,取自实测数据而非发明。
///
/// 该字段是 quarantine receipt 的必填分类:缺失或越出封闭字母表均 fail-closed。
/// 三条测试分别钉住缺失、已知全集 round-trip 与未知值拒绝。
///
/// 夹具沿用同目录 <c>DigestionQuarantineTests</c> 的 <c>Atom</c> / <c>DirectorySnapshot</c>
/// 形态(partial class 共享),不另造一套。
/// </summary>
public sealed partial class DigestionQuarantineTests
{
    private const string ClassifiedQuarantine = """
        quarantine:
          justification: interpretive statement has no machine predicate
          reentry_condition: typed predicate or frozen witness
          blocker_class: already-covered
        """;

    [Theory]
    [InlineData("already-covered")]
    [InlineData("missing-prerequisite")]
    [InlineData("multi-clause-guard")]
    public void LoaderAcceptsAndRoundTripsEachKnownBlockerClass(string blockerClass)
    {
        var quarantine = ClassifiedQuarantine.Replace(
            "already-covered",
            blockerClass,
            StringComparison.Ordinal);
        var document = BackfillInventoryLoader.Load(
            DirectorySnapshot(Atom(AtomId, quarantine)));
        var entry = Assert.Single(document.RequireDigestionEntries());

        Assert.Equal(blockerClass, entry.Receipts.Quarantine!.BlockerClass);

        var atomText = Encoding.UTF8.GetString(
            BackfillInventoryWriter.WriteAtom(entry).AsSpan());
        Assert.Contains($"blocker_class: {blockerClass}", atomText, StringComparison.Ordinal);
        Assert.Equal(
            entry,
            Assert.Single(BackfillInventoryLoader.Load(DirectorySnapshot(atomText))
                .RequireDigestionEntries()));
    }

    // 字母表封闭且 fail-closed。放行任意字符串等于退回自由文本,而那正是 #2137 要治的病:
    // 分类的全部价值在于可被机器统计与比较。
    [Fact]
    public void LoaderRejectsABlockerClassOutsideTheClosedAlphabet()
    {
        var quarantine = ClassifiedQuarantine.Replace(
            "already-covered",
            "made-up-class",
            StringComparison.Ordinal);

        var error = Assert.Throws<FormatException>(() =>
            BackfillInventoryLoader.Load(DirectorySnapshot(Atom(AtomId, quarantine)))
                .RequireDigestionEntries());

        Assert.Contains("made-up-class", error.Message, StringComparison.Ordinal);
        Assert.Contains("already-covered", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void LoaderRejectsAQuarantineWithoutABlockerClass()
    {
        const string quarantine = """
            quarantine:
              justification: interpretive statement has no machine predicate
              reentry_condition: typed predicate or frozen witness
            """;

        var error = Assert.Throws<FormatException>(() =>
            BackfillInventoryLoader.Load(DirectorySnapshot(Atom(AtomId, quarantine)))
                .RequireDigestionEntries());

        Assert.Contains("blocker_class", error.Message, StringComparison.Ordinal);
    }
}
