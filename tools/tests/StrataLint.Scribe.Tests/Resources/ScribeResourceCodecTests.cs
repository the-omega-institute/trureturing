using System.Text;
using StrataLint.Scribe;

namespace StrataLint.Scribe.Tests.Resources;

public sealed class ScribeResourceCodecTests
{
    [Fact]
    public void CodecRoundTripsDefinitionAndProducesStableUtf8()
    {
        var definition = DocumentDefinition.Create(
            ScribeNode.Create(
                "resource-digest",
                DefinitionDsl.H("Resource"),
                DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("hello"))),
                sourcePath: "Blueprint/D5/S1/Scale/Resource.scribe.cs"),
            "Blueprint/D5/S1/Scale/Resource.scribe.cs");

        var encoded = ScribeResourceCodec.Encode(definition);
        var decoded = ScribeResourceCodec.Decode(encoded);

        Assert.Equal(encoded, ScribeResourceCodec.Encode(decoded));
        Assert.Equal("D5/S1/Scale/Resource", decoded.Document.Header.Gid.Value);
        Assert.Equal("Blueprint/D5/S1/Scale/Resource.scribe.cs", decoded.SourcePath);
    }

    [Fact]
    public void CodecRejectsUnknownTypeWithNamedReason()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "{\"schema\":\"trureturing.scribe.document-definition\",\"version\":1,\"document\":{\"type\":\"unknown\"},\"sourcePath\":\"Blueprint/D5/S1/Resource.scribe.cs\"}");

        var error = Assert.Throws<ScribeResourceException>(() => ScribeResourceCodec.Decode(bytes));

        Assert.Equal(ScribeResourceErrorCode.UnknownType, error.ReasonCode);
    }
}
