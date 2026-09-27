using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class FormalizeCandidatesTests
{
    [Fact]
    public void FormalizeCandidatesRetainScopedTableConclusionAndProof()
    {
        const string body = "假设 α > 0。\n\n"
            + "| 条件 | 值 |\n| --- | --- |\n| 正 | α |\n\n"
            + "因此结论严格成立：\n\n$$\nF(α) > 0\n$$\n\n"
            + "*证明*。使用表中条件并取极限。证毕。";
        var entry = Entry("source", "scoped-table", "命题", "6.1", body: body,
            atomizer: AtomizerRegistry.GenericId);

        var result = Run([entry], atomizer: AtomizerRegistry.GenericId);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        var candidate = Assert.Single(json.RootElement.GetProperty("candidates").EnumerateArray());
        Assert.Equal("命题", candidate.GetProperty("kind").GetString());
        Assert.Equal("**命题 6.1**。" + body + "\n", candidate.GetProperty("atom_text").GetString());
        Assert.Equal(Encoding.UTF8.GetString(entry.Atom.RawBytes.AsSpan()), candidate.GetProperty("atom_text").GetString());
        Assert.Empty(json.RootElement.GetProperty("withheld").EnumerateArray());
    }
}
