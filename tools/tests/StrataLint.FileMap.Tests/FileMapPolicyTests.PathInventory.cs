using System.Text;
using StrataLint.Engine;
using Xunit;

namespace StrataLint.FileMap.Tests;

public sealed partial class FileMapPolicyTests
{
    [Theory]
    [InlineData("[]")]
    [InlineData("[\"docs/**\", \"tools/**\"]")]
    public void ResourcePathInventorySurvivesCanonicalPolicyRoundTrip(string inventory)
    {
        var source = InventoryResourceSource(inventory);
        var first = FileMapLoader.Parse(Encoding.UTF8.GetBytes(source), "fixture.toml");
        var canonical = FileMapCanonicalWriter.Write(first);
        var second = FileMapLoader.Parse(canonical.AsSpan(), "fixture.toml");
        Assert.False(Assert.Single(first.Resources).PathInventory.IsDefault);
        Assert.Equal(Assert.Single(first.Resources).PathInventory.ToArray(), Assert.Single(second.Resources).PathInventory.ToArray());
        Assert.Equal(canonical.ToArray(), FileMapCanonicalWriter.Write(second).ToArray());
    }

    [Theory]
    [InlineData("\"docs/**\"", "engineering")]
    [InlineData("[1]", "engineering")]
    [InlineData("[\"docs/**\", \"docs/**\"]", "engineering")]
    [InlineData("[\"tools/**\", \"docs/**\"]", "engineering")]
    [InlineData("[\"docs/**\"]", "current")]
    public void InvalidResourcePathInventoryIsRejected(string inventory, string stage)
    {
        var error = Assert.Throws<FormatException>(() => FileMapLoader.Parse(
            Encoding.UTF8.GetBytes(InventoryResourceSource(inventory, stage)), "fixture.toml"));
        Assert.Contains("path_inventory", error.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("[]")]
    [InlineData("[\"docs/**\", \"tools/**\"]")]
    public void ResourcePathInputsSurviveCanonicalPolicyRoundTrip(string inputs)
    {
        var source = InventoryResourceSource(inputs).Replace("path_inventory =", "path_inputs =", StringComparison.Ordinal);
        var first = FileMapLoader.Parse(Encoding.UTF8.GetBytes(source), "fixture.toml");
        var canonical = FileMapCanonicalWriter.Write(first);
        var second = FileMapLoader.Parse(canonical.AsSpan(), "fixture.toml");
        Assert.False(Assert.Single(first.Resources).PathInputs.IsDefault);
        Assert.True(Assert.Single(second.Resources).PathInventory.IsDefault);
        Assert.Equal(Assert.Single(first.Resources).PathInputs.ToArray(), Assert.Single(second.Resources).PathInputs.ToArray());
        Assert.Equal(canonical.ToArray(), FileMapCanonicalWriter.Write(second).ToArray());
    }

    [Theory]
    [InlineData("\"docs/**\"", "engineering")]
    [InlineData("[1]", "engineering")]
    [InlineData("[\"docs/**\", \"docs/**\"]", "engineering")]
    [InlineData("[\"tools/**\", \"docs/**\"]", "engineering")]
    [InlineData("[\"docs/**\"]", "current")]
    public void InvalidResourcePathInputsAreRejected(string inputs, string stage)
    {
        var source = InventoryResourceSource(inputs, stage).Replace("path_inventory =", "path_inputs =", StringComparison.Ordinal);
        var error = Assert.Throws<FormatException>(() => FileMapLoader.Parse(Encoding.UTF8.GetBytes(source), "fixture.toml"));
        Assert.Contains("path_inputs", error.Message, StringComparison.Ordinal);
    }

    private static string InventoryResourceSource(string inventory, string stage = "engineering")
    {
        var manifest = Parse(Entry("**", "program", "none", "reader", "dotnet-test"));
        return Encoding.UTF8.GetString(FileMapCanonicalWriter.Write(manifest).AsSpan()).Replace("resources = [\n]",
            "resources = [{ id = \"inventory\", stage = \"" + stage + "\", owner = \"tools/owner.cs\", prerequisites = [], tools = [], cache_layers = [], cache_activation = {}, materials = [], path_inventory = "
            + inventory + " }]", StringComparison.Ordinal);
    }
}
