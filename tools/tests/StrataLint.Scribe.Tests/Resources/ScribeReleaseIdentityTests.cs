using System.Text;
using System.Text.Json.Nodes;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeReleaseIdentityTests
{
    private const string Valid = """
        {"schema":"trureturing.scribe.release-identity","sourceCommit":"0123456789abcdef0123456789abcdef01234567","packFormatVersion":1,"entryCount":2,"totalSha256":"abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789"}
        """;

    [Theory]
    [InlineData("schema")]
    [InlineData("sourceCommit")]
    [InlineData("packFormatVersion")]
    [InlineData("entryCount")]
    [InlineData("totalSha256")]
    public void DecodeRejectsMissingField(string field)
    {
        var json = JsonNode.Parse(Valid)!.AsObject();
        json.Remove(field);
        Reject(json.ToJsonString(), "MissingField");
    }

    [Fact]
    public void DecodeRejectsExtraField()
    {
        var json = JsonNode.Parse(Valid)!.AsObject();
        json["extra"] = "value";
        Reject(json.ToJsonString(), "ExtraField");
    }

    [Fact]
    public void DecodeRejectsDuplicateField() => Reject(Valid.Replace("\"entryCount\":2",
        "\"entryCount\":2,\"entryCount\":2", StringComparison.Ordinal), "DuplicateField");

    [Theory]
    [InlineData("schema", "null", "InvalidType")]
    [InlineData("schema", "3", "InvalidType")]
    [InlineData("schema", "\"other\"", "SchemaMismatch")]
    [InlineData("sourceCommit", "null", "InvalidType")]
    [InlineData("sourceCommit", "7", "InvalidType")]
    [InlineData("sourceCommit", "\"0123456789ABCDEF0123456789abcdef01234567\"", "InvalidSourceCommit")]
    [InlineData("sourceCommit", "\"0123\"", "InvalidSourceCommit")]
    [InlineData("sourceCommit", "\"g123456789abcdef0123456789abcdef01234567\"", "InvalidSourceCommit")]
    [InlineData("packFormatVersion", "\"1\"", "InvalidType")]
    [InlineData("packFormatVersion", "null", "InvalidType")]
    [InlineData("packFormatVersion", "1.5", "InvalidType")]
    [InlineData("packFormatVersion", "2147483648", "InvalidType")]
    [InlineData("packFormatVersion", "-1", "InvalidPackFormatVersion")]
    [InlineData("packFormatVersion", "0", "InvalidPackFormatVersion")]
    [InlineData("entryCount", "\"2\"", "InvalidType")]
    [InlineData("entryCount", "null", "InvalidType")]
    [InlineData("entryCount", "1.5", "InvalidType")]
    [InlineData("entryCount", "2147483648", "InvalidType")]
    [InlineData("entryCount", "-1", "InvalidEntryCount")]
    [InlineData("totalSha256", "null", "InvalidType")]
    [InlineData("totalSha256", "5", "InvalidType")]
    [InlineData("totalSha256", "\"0123456789ABCDEF0123456789abcdef01234567456789abcdef0123456789\"", "InvalidTotalSha256")]
    [InlineData("totalSha256", "\"abcd\"", "InvalidTotalSha256")]
    [InlineData("totalSha256", "\"gbcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789\"", "InvalidTotalSha256")]
    public void DecodeRejectsInvalidField(string field, string value, string reason)
    {
        var json = JsonNode.Parse(Valid)!.AsObject();
        json[field] = JsonNode.Parse(value);
        Reject(json.ToJsonString(), reason);
    }

    [Theory]
    [InlineData("{")]
    [InlineData("[]")]
    [InlineData("null")]
    public void DecodeRejectsInvalidJson(string text) => Reject(text, "InvalidJson");

    [Fact]
    public void EncodingIsCanonicalDeterministicAndRoundTrips()
    {
        var identity = ScribeReleaseSurface.Decode(Encoding.UTF8.GetBytes(Valid));
        var first = ScribeReleaseSurface.Encode(identity);
        Assert.Equal(Encoding.UTF8.GetBytes(Valid), first);
        Assert.Equal(first, ScribeReleaseSurface.Encode(identity));
        Assert.Equal(identity, ScribeReleaseSurface.Decode(first));
        var reordered = JsonNode.Parse(Valid)!.AsObject().Reverse()
            .Select(item => KeyValuePair.Create(item.Key, item.Value?.DeepClone())).ToArray();
        Assert.Equal(first, ScribeReleaseSurface.Encode(ScribeReleaseSurface.Decode(
            Encoding.UTF8.GetBytes(new JsonObject(reordered).ToJsonString()))));
    }

    private static void Reject(string text, string reason)
    {
        var exception = Assert.ThrowsAny<FormatException>(() => ScribeReleaseSurface.Decode(Encoding.UTF8.GetBytes(text)));
        Assert.StartsWith(reason + ":", exception.Message, StringComparison.Ordinal);
    }
}
