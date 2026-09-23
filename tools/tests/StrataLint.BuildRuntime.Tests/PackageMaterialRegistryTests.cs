using System.Text.Json;
using StrataLint.EngineeringScope;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.BuildRuntime.Tests;

public sealed class PackageMaterialRegistryTests
{
    [Fact]
    public void AssetsFileInventoryDoesNotSelectDeclaredMaterial()
    {
        using var fixture = new Fixture();
        fixture.WriteAssets(fixture.AssetsPath, ["alpha/1.0.0", "beta/2.0.0"], emptyInventory: true);
        Assert.Equal(fixture.ExpectedRelative, PackageMaterialRegistry.Expand(fixture.Root, fixture.PackageRoot).Select(item => item.Relative));
        File.WriteAllText(fixture.AssetsPath, "not JSON; must never be parsed");
        Assert.Equal(fixture.ExpectedRelative, PackageMaterialRegistry.Expand(fixture.Root, fixture.PackageRoot).Select(item => item.Relative));
        File.Delete(fixture.AssetsPath);
        Assert.Equal(fixture.ExpectedRelative, PackageMaterialRegistry.Expand(fixture.Root, fixture.PackageRoot).Select(item => item.Relative));
    }

    [Theory]
    [InlineData("alpha/1.0.0/.nupkg.metadata")]
    [InlineData("alpha/1.0.0/alpha.nuspec")]
    [InlineData("alpha/1.0.0/lib/net10.0/alpha.dll")]
    [InlineData("beta/2.0.0/beta.dll")]
    public void EachDeclaredRequiredMaterialMustExist(string missing)
    {
        using var fixture = new Fixture();
        File.Delete(Path.Combine(fixture.PackageRoot, missing));
        var error = Assert.Throws<InvalidDataException>(() => PackageMaterialRegistry.Expand(fixture.Root, fixture.PackageRoot).ToArray());
        Assert.Contains("material", error.Message, StringComparison.Ordinal);
        Assert.Contains(string.Join('/', missing.Split('/').Take(2)), error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void EmptyRequiredGlobIsRejectedEvenWhenOtherMaterialExists()
    {
        using var fixture = new Fixture();
        fixture.WriteAssets(fixture.AssetsPath, ["alpha/1.0.0", "beta/2.0.0"], emptyInventory: true);
        fixture.WriteRegistry("""[{"packagePath":"alpha/1.0.0","include":["alpha.nuspec","missing/*.dll"],"exclude":[]}]""");
        var error = Assert.Throws<InvalidDataException>(() => PackageMaterialRegistry.Expand(fixture.Root, fixture.PackageRoot).ToArray());
        Assert.Contains("missing/*.dll", error.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("duplicate-package")]
    [InlineData("conflicting-pattern")]
    [InlineData("duplicate-pattern")]
    [InlineData("invalid-package")]
    [InlineData("invalid-pattern")]
    [InlineData("empty-include")]
    [InlineData("extra-field")]
    [InlineData("duplicate-field")]
    [InlineData("wrong-schema-type")]
    [InlineData("malformed-json")]
    public void ProductionParserRejectsInvalidManifest(string defect)
    {
        using var fixture = new Fixture();
        const string row = """{"packagePath":"alpha/1.0.0","include":["alpha.nuspec"],"exclude":[]}""";
        fixture.WriteRegistry("[" + row + "]");
        var json = File.ReadAllText(fixture.ManifestPath);
        json = defect switch
        {
            "duplicate-package" => json.Replace(row, row + "," + row, StringComparison.Ordinal),
            "conflicting-pattern" => json.Replace("\"exclude\":[]", "\"exclude\":[\"alpha.nuspec\"]", StringComparison.Ordinal),
            "duplicate-pattern" => json.Replace("[\"alpha.nuspec\"]", "[\"alpha.nuspec\",\"alpha.nuspec\"]", StringComparison.Ordinal),
            "invalid-package" => json.Replace("alpha/1.0.0", "../escape", StringComparison.Ordinal),
            "invalid-pattern" => json.Replace("alpha.nuspec", "../*.dll", StringComparison.Ordinal),
            "empty-include" => json.Replace("[\"alpha.nuspec\"]", "[]", StringComparison.Ordinal),
            "extra-field" => json.Replace("\"schemaVersion\":1", "\"extra\":true,\"schemaVersion\":1", StringComparison.Ordinal),
            "duplicate-field" => json.Replace("\"schemaVersion\":1", "\"schemaVersion\":1,\"schemaVersion\":1", StringComparison.Ordinal),
            "wrong-schema-type" => json.Replace("\"schemaVersion\":1", "\"schemaVersion\":\"1\"", StringComparison.Ordinal),
            "malformed-json" => "{",
            _ => throw new ArgumentException(defect),
        };
        File.WriteAllText(fixture.ManifestPath, json);
        Assert.Throws<InvalidDataException>(() => PackageMaterialRegistry.Load(fixture.Root));
    }

    [Fact]
    public void MissingManifestIsRejected()
    {
        using var fixture = new Fixture();
        File.Delete(fixture.ManifestPath);
        Assert.Throws<InvalidDataException>(() => PackageMaterialRegistry.Load(fixture.Root));
    }

    [Theory]
    [InlineData("")]
    [InlineData("relative/packages")]
    public void ExpansionRequiresAnExplicitAbsoluteProducerRoot(string packageRoot)
    {
        using var fixture = new Fixture();
        Assert.Contains("absolute producer-supplied", Assert.Throws<InvalidDataException>(() =>
            PackageMaterialRegistry.Expand(fixture.Root, packageRoot).ToArray()).Message, StringComparison.Ordinal);
    }

    private sealed class Fixture : IDisposable
    {
        private readonly TemporaryDirectory candidate = new();
        internal string Root => candidate.Path;
        internal string PackageRoot => Path.Combine(Root, "build/producer-packages");
        internal string AssetsPath => Path.Combine(Root, "build/project.assets.json");
        internal string ManifestPath => Path.Combine(Root, PackageMaterialRegistry.RelativePath);
        internal string[] ExpectedRelative { get; } = ["alpha/1.0.0/.nupkg.metadata", "alpha/1.0.0/alpha.nuspec", "alpha/1.0.0/lib/net10.0/alpha.dll", "beta/2.0.0/beta.dll"];

        internal Fixture()
        {
            Write(".gitignore", ".lake/\nbuild/\n**/bin/\n**/obj/\n");
            WriteRegistry("""
                [{"packagePath":"alpha/1.0.0","include":["**/*",".nupkg.metadata","alpha.nuspec","lib/**/*.dll"],"exclude":["**/*.nupkg","**/*.snupkg"]},
                 {"packagePath":"beta/2.0.0","include":["beta.dll"],"exclude":[]}]
                """);
            foreach (var path in ExpectedRelative) WritePackage(path);
            WriteAssets(AssetsPath, ["alpha/1.0.0", "beta/2.0.0"]);
        }

        internal void WriteRegistry(string packages) => Write(PackageMaterialRegistry.RelativePath,
            "{\"schemaVersion\":1,\"packageRootSource\":\"build-output:NuGetPackageRoot\",\"packages\":" + packages + "}");
        internal void WritePackage(string path) => Write("build/producer-packages/" + path, "fixture:" + path);
        internal void WriteAssets(string path, string[] packages, bool emptyInventory = false)
        {
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, JsonSerializer.Serialize(new {
                packageFolders = new Dictionary<string, object> { [PackageRoot] = new { } },
                libraries = packages.ToDictionary(package => package, package => new {
                    type = "package", path = package, files = emptyInventory ? [] : ExpectedRelative
                        .Where(file => file.StartsWith(package + "/", StringComparison.Ordinal)).Select(file => file[(package.Length + 1)..]).ToArray() }) }));
        }
        internal void Write(string path, string text)
        {
            var full = Path.Combine(Root, path);
            Directory.CreateDirectory(Path.GetDirectoryName(full)!);
            File.WriteAllText(full, text);
        }
        public void Dispose() => candidate.Dispose();
    }
}
