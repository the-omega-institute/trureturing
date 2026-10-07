using System.Text.Json.Nodes;
using StrataLint.Engineering;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.Engineering.Tests;

public sealed class EngineeringProjectSchemaTests
{
    private static string Manifest() => EngineeringRegistrationFixture.Manifest(
        new EngineeringProjectFixture("odd/Program.csproj", "Explicit.Checks", "cross-cutting-test", ["missing/Source.cs"],
            References: ["unavailable/Dependency.csproj"]));

    [Fact]
    public void IdentityDecodeRequiresNoSourceInventoryOrDependencyGraph()
    {
        var declaration = Assert.Single(EngineeringProjectSchema.Parse(Manifest()).Projects);
        Assert.Equal("Explicit.Checks", declaration.Assembly);
        Assert.True(declaration.IsTest);
        Assert.Equal(["unavailable/Dependency.csproj"], declaration.References);
    }

    [Theory]
    [InlineData("assembly", "null")]
    [InlineData("assembly", "\" \"")]
    [InlineData("path", "\"../Outside.csproj\"")]
    [InlineData("role", "\"test\"")]
    [InlineData("references", "[\"a.csproj\",\"a.csproj\"]")]
    [InlineData("owner", "{\"path\":\"p.csproj\",\"assembly\":\"P\"}")]
    [InlineData("test_partition", "null")]
    public void MalformedConsumedIdentityFails(string field, string value)
    {
        var manifest = JsonNode.Parse(Manifest())!;
        manifest["projects"]![0]![field] = JsonNode.Parse(value);
        Assert.Throws<InvalidDataException>(() => EngineeringProjectSchema.Parse(manifest.ToJsonString()));
    }

    [Theory]
    [InlineData("assembly")]
    [InlineData("references")]
    [InlineData("root_namespace")]
    public void EveryRequiredWireFieldRemainsRequired(string field)
    {
        var manifest = JsonNode.Parse(Manifest())!;
        manifest["projects"]![0]!.AsObject().Remove(field);
        Assert.Throws<InvalidDataException>(() => EngineeringProjectSchema.Parse(manifest.ToJsonString()));
    }

    [Fact]
    public void DuplicateAndUnknownWirePropertiesReject()
    {
        Assert.Throws<InvalidDataException>(() => EngineeringProjectSchema.Parse(
            Manifest().Replace("\"assembly\":", "\"assembly\":\"Other\",\"assembly\":", StringComparison.Ordinal)));
        var manifest = JsonNode.Parse(Manifest())!;
        manifest["discovery"] = true;
        Assert.Throws<InvalidDataException>(() => EngineeringProjectSchema.Parse(manifest.ToJsonString()));
    }

    [Fact]
    public void HistoricalProjectionSkipsOnlyUnconsumedFields()
    {
        var manifest = JsonNode.Parse(Manifest())!;
        manifest["projects"]![0]!["ci"] = true;
        Assert.Single(EngineeringProjectSchema.ParseBase(manifest.ToJsonString()));
        Assert.Throws<InvalidDataException>(() => EngineeringProjectSchema.Parse(manifest.ToJsonString()));
        manifest["projects"]![0]!.AsObject().Remove("assembly");
        Assert.Throws<InvalidDataException>(() => EngineeringProjectSchema.ParseBase(manifest.ToJsonString()));
    }
}
