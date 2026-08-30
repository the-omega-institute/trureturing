using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

// 拆自 FormalizeCandidatesTests.cs(2026-08-30,#4125 pass 4):主文件加入本测试后 804 行,越过 SL-003 的 800 硬线。
public sealed partial class FormalizeCandidatesTests
{
    // Hermetic(#4125 pass 5,quality 席四轮坚持,接受):原子化走 GenericId(TheoryAtomizerRules.None),
    // 合成仓库里的规则文件用 TheoryAtomizerDataTests.Minimal(既有的最小合法文档),Run 的 rulesBytes 覆盖使
    // DigestionTestSupport.RulesBytes 的 canonical 文件读取根本不发生——把测试 DLL 拷到任何仓库之外也能跑。
    [Fact]
    public void FormalizeCandidatesProjectsQuarantineInsteadOfOfferingTheAtom()
    {
        var entry = Entry("source", "quarantined", "theorem", "1.0", atomizer: AtomizerRegistry.GenericId);
        var ledger = Ledger([entry], AtomizerRegistry.GenericId);
        var source = Assert.Single(ledger.RequireDigestionSources());
        var stored = Assert.Single(source.Entries);
        ledger = ledger.WithDigestionSources(
        [
            source with
            {
                Entries =
                [
                    stored with
                    {
                        Receipts = stored.Receipts with
                        {
                            Quarantine = new DigestionQuarantine(
                                "missing spectral owner",
                                "public spectral owner exists",
                                "missing-prerequisite"),
                        },
                    },
                ],
            },
        ]);

        var result = Run(
            [entry],
            ledger: ledger,
            atomizer: AtomizerRegistry.GenericId,
            rulesBytes: Encoding.UTF8.GetBytes(TheoryAtomizerDataTests.Minimal));

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal("stratalint-formalize-candidates-v4", json.RootElement.GetProperty("schema").GetString());
        Assert.Empty(json.RootElement.GetProperty("candidates").EnumerateArray());
        var quarantined = Assert.Single(
            json.RootElement.GetProperty("quarantined").EnumerateArray());
        Assert.Equal("source", quarantined.GetProperty("source_id").GetString());
        Assert.Equal("quarantined", quarantined.GetProperty("atom_id").GetString());
        Assert.Equal("theorem/1.0", quarantined.GetProperty("ast_path").GetString());
        Assert.Equal(
            "missing-prerequisite",
            quarantined.GetProperty("blocker_class").GetString());
        Assert.Equal(
            "missing spectral owner",
            quarantined.GetProperty("justification").GetString());
        Assert.Equal(
            "public spectral owner exists",
            quarantined.GetProperty("reentry_condition").GetString());
    }

}
