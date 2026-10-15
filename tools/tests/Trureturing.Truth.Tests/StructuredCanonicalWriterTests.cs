using System.Text;
using System.Text.Encodings.Web;
using System.Text.Json;
using Xunit;

namespace Trureturing.Truth.Tests;

public sealed class StructuredCanonicalWriterTests
{
    private static readonly JsonSerializerOptions StringOptions = new()
    {
        Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping,
    };

    public static IEnumerable<object[]> Strings()
    {
        yield return [""];
        yield return ["ASCII </script> & + / \\\"\r\n\t\b\f"];
        yield return ["中文 αβ e\u0301 \u2028\u2029\u00a0\uE000\uFFFF 😀 \U00010000\U0010FFFF"];
        yield return [new string(Enumerable.Range(0, 0x10000).Select(static i => (char)i).ToArray())];
        foreach (var offset in new[] { 16382, 16383, 16384, 32767 })
        {
            yield return [new string('a', offset) + "😀\"\\\n中文" + new string('z', 17000)];
            yield return [new string('a', offset) + "\uD800x\uDC00" + new string('z', 17000)];
        }
    }

    [Theory]
    [MemberData(nameof(Strings))]
    public void StringObjectsMatchTheOriginalSerializerAndCanonicalWriter(string value)
    {
        var properties = new Dictionary<string, string?>
        {
            ["z"] = value,
            ["é😀\"\\\n"] = value,
            ["a"] = null,
            [value] = "property name",
        };
        var expected = LegacyStringObject(properties);

        var actual = StructuredCanonicalWriter.WriteJson(properties);
        var parsed = StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(properties));

        Assert.Equal(expected, actual.ToArray());
        Assert.Equal(expected, parsed.ToArray());
        Assert.Equal(actual.ToArray(), StructuredCanonicalWriter.WriteJson(
            new UTF8Encoding(false, true).GetString(actual.AsSpan())).ToArray());
    }

    [Fact]
    public void JsonKeepsCanonicalOrderingSpacingEscapingNumbersAndFinalLf()
    {
        const string input = """
            {"z": [true, false, null, -0.0, 1.2300, 1e-28, "😀", "\n\t\\\""],
             "a": {"β": "中文", "<": "/ & +"}}
            """;
        const string expected = """
            {"a": {"<": "/ & +", "β": "中文"}, "z": [true, false, null, 0, 1.23, 1e-28, "\uD83D\uDE00", "\n\t\\\""]}
            """ + "\n";

        Assert.Equal(Encoding.UTF8.GetBytes(expected), StructuredCanonicalWriter.WriteJson(input).ToArray());
        Assert.Equal("{}\n"u8.ToArray(), StructuredCanonicalWriter.WriteJson(
            new Dictionary<string, string?>()).ToArray());
    }

    [Theory]
    [InlineData("{\"a\": 1, \"a\": 2}")]
    [InlineData("{\"a\": 1e100}")]
    public void JsonStillRejectsDuplicateKeysAndNumbersOutsideTheCanonicalDomain(string input) =>
        Assert.Throws<FormatException>(() => StructuredCanonicalWriter.WriteJson(input));

    private static byte[] LegacyStringObject(Dictionary<string, string?> properties)
    {
        // The original two-stage implementation is the compatibility oracle.
        var element = JsonSerializer.SerializeToElement(properties);
        var builder = new StringBuilder("{");
        var index = 0;
        foreach (var property in element.EnumerateObject().OrderBy(static p => p.Name, StringComparer.Ordinal))
        {
            if (index++ > 0) builder.Append(", ");
            builder.Append(JsonSerializer.Serialize(property.Name, StringOptions)).Append(": ");
            builder.Append(JsonSerializer.Serialize(property.Value.GetString(), StringOptions));
        }
        builder.Append("}\n");
        return new UTF8Encoding(false, true).GetBytes(builder.ToString());
    }
}
