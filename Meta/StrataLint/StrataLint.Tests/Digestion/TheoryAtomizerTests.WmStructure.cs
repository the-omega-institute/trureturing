using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class TheoryAtomizerTests
{
    public static TheoryData<string, byte[]> InvalidWmSources
    {
        get
        {
            var canonical = CanonicalWmFixture();
            return new TheoryData<string, byte[]>
            {
                { "missing H1", Encoding.UTF8.GetBytes(canonical.Replace(WmTitle + "\n", "BEDC-WM\n", StringComparison.Ordinal)) },
                { "missing section 7 appendix", Encoding.UTF8.GetBytes(canonical.Replace(WmAppendix, string.Empty, StringComparison.Ordinal)) },
                { "missing audit", Encoding.UTF8.GetBytes(canonical[..canonical.IndexOf("## 校核记录", StringComparison.Ordinal)]) },
                { "duplicate or out-of-order section", Encoding.UTF8.GetBytes(canonical.Replace("## 5. Section 5", "## 4. Section 5", StringComparison.Ordinal)) },
                { "unknown heading", Encoding.UTF8.GetBytes(canonical.Replace("## 6. Section 6", "## Unknown", StringComparison.Ordinal)) },
                { "leading conversation residue", Encoding.UTF8.GetBytes("可以。\n" + canonical) },
                { "missing discipline", Encoding.UTF8.GetBytes(canonical.Replace(WmDiscipline, string.Empty, StringComparison.Ordinal)) },
                { "replaced discipline", Encoding.UTF8.GetBytes(canonical.Replace("> 纪律:", "> 建议:", StringComparison.Ordinal)) },
                { "duplicate discipline", Encoding.UTF8.GetBytes(canonical.Replace(WmDiscipline, WmDiscipline + "\n" + WmDiscipline, StringComparison.Ordinal)) },
                { "audit trailing conversation LF", Encoding.UTF8.GetBytes(canonical + "可以。\n") },
                { "audit trailing conversation CRLF", Encoding.UTF8.GetBytes(canonical.ReplaceLineEndings("\r\n") + "可以。\r\n") },
                { "audit trailing conversation CR", Encoding.UTF8.GetBytes(canonical.ReplaceLineEndings("\r") + "可以。\r") },
                {
                    "audit same-line trailing sentence",
                    Encoding.UTF8.GetBytes(canonical.Replace(
                        WmCurrentTodoClosure,
                        WmCurrentTodoClosure + "可以。",
                        StringComparison.Ordinal))
                },
                {
                    "current-todo true-volume trailing conversation",
                    Encoding.UTF8.GetBytes(canonical.Replace(
                        WmCurrentTodoClosure,
                        WmCurrentTodoClosure + "这部分内容 我希望能够加入到trueturning 你觉得是否合适",
                        StringComparison.Ordinal))
                },
                { "current-todo trailing fenced conversation block", Encoding.UTF8.GetBytes(canonical + "\n```text\nassistant: 可以。\n```\n") },
                { "current-todo trailing Markdown table", Encoding.UTF8.GetBytes(canonical + "\n| role | content |\n| --- | --- |\n| assistant | 可以。 |\n") },
                {
                    "current-todo replayed closure marker",
                    Encoding.UTF8.GetBytes(canonical.Replace(
                        WmCurrentTodoClosure,
                        WmCurrentTodoClosure + "可以。" + WmCurrentTodoClosure,
                        StringComparison.Ordinal))
                },
                { "v0.2 audit trailing conversation LF", Encoding.UTF8.GetBytes(CanonicalWmV02Fixture() + "可以。\n") },
                { "v0.2 audit trailing conversation CRLF", Encoding.UTF8.GetBytes(CanonicalWmV02Fixture().ReplaceLineEndings("\r\n") + "可以。\r\n") },
                { "v0.2 audit trailing conversation CR", Encoding.UTF8.GetBytes(CanonicalWmV02Fixture().ReplaceLineEndings("\r") + "可以。\r") },
                {
                    "v0.2 audit same-line trailing sentence",
                    Encoding.UTF8.GetBytes(CanonicalWmV02Fixture().Replace(
                        "旧块不改。\n",
                        "旧块不改。可以。\n",
                        StringComparison.Ordinal))
                },
                { "v0.2 audit trailing fenced conversation block", Encoding.UTF8.GetBytes(CanonicalWmV02Fixture() + "\n```text\nassistant: 可以。\n```\n") },
                { "v0.2 audit trailing Markdown table", Encoding.UTF8.GetBytes(CanonicalWmV02Fixture() + "\n| role | content |\n| --- | --- |\n| assistant | 可以。 |\n") },
                {
                    "v0.2 audit replayed closure marker",
                    Encoding.UTF8.GetBytes(CanonicalWmV02Fixture().Replace(
                        "旧块不改。\n",
                        "旧块不改。可以。旧块不改。\n",
                        StringComparison.Ordinal))
                },
                { "non-UTF-8", [0xff, 0xfe, 0xfd] },
            };
        }
    }

    [Theory]
    [InlineData("\n")]
    [InlineData("\r\n")]
    [InlineData("\r")]
    public void WmV1AcceptsSupportedLineEndings(string lineEnding)
    {
        var canonical = AtomizerRegistry.Atomize(
            AtomizerRegistry.WmId,
            Encoding.UTF8.GetBytes(CanonicalWmFixture().ReplaceLineEndings(lineEnding)));
        var evolved = AtomizerRegistry.Atomize(
            AtomizerRegistry.WmId,
            Encoding.UTF8.GetBytes(CanonicalWmV02Fixture().ReplaceLineEndings(lineEnding)));

        Assert.Equal(18, canonical.Claims.Length);
        Assert.Equal(20, evolved.Claims.Length);
    }
}
