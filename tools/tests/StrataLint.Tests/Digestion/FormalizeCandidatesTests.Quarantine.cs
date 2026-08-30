using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

// 拆自 FormalizeCandidatesTests.cs(2026-08-30,#4125 pass 4):主文件加入本测试后 804 行,越过 SL-003 的 800 硬线。
public sealed partial class FormalizeCandidatesTests
{
    // 走 GenericId 原子器(同类既有测试 FormalizeCandidatesKindAlphabetIsClosed 的先例):Entry/Run 的原子化
    // 取 TheoryAtomizerRules.None,不读 canonical `Meta/theory-atomizers.toml`(#4125 pass-2 quality 席)。
    // Run 仍把 canonical 规则字节注入合成仓库(`TheoryAtomizerDataLoader.DataPath`)——那是本类全部 51 条测试共用的
    // 夹具层;一份 hermetic 的规则文件须满足 TheoryAtomizerDataLoader 全部必需 section 的行文法(canonical 文件 907 行),
    // 是独立的夹具工程,不在本测试的射程内(#4125 quality 席两轮提出,如实记为未做)。
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

        var result = Run([entry], ledger: ledger, atomizer: AtomizerRegistry.GenericId);

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
