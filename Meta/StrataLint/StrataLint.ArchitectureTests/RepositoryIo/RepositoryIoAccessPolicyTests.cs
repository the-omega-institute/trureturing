namespace StrataLint.ArchitectureTests;

public sealed class RepositoryIoAccessPolicyTests
{
    [Fact]
    public void ScribeTestsRepositoryIoIsConfinedToNamedGateways()
    {
        var findings = RepositoryIoAccessPolicy.InspectRepository(RepositoryLayout.FindRoot());

        Assert.True(findings.Count == 0, string.Join(Environment.NewLine, findings));
    }

    [Fact]
    public void DeferredProjectExemptionsArePinnedAndMayOnlyShrink()
    {
        Assert.Equal(
            ["StrataLint.ArchitectureTests", "StrataLint.Tests"],
            RepositoryIoAccessPolicy.DeferredProjectExemptions.Order(StringComparer.Ordinal));
    }

    [Theory]
    [InlineData("class C { string Read() => File.ReadAllText(\"x\"); }", "System.IO.File.ReadAllText")]
    [InlineData("class C { object Read() => Directory.EnumerateFiles(\"x\"); }", "System.IO.Directory.EnumerateFiles")]
    [InlineData("class C { object Read() => new FileStream(\"x\", FileMode.Open); }", "System.IO.FileStream")]
    [InlineData("class C { object Read() => new StreamReader(\"x\"); }", "System.IO.StreamReader")]
    [InlineData("class C { object Read() => new StreamWriter(\"x\"); }", "System.IO.StreamWriter")]
    [InlineData("class C { object Read() => XDocument.Load(\"x\"); }", "System.Xml.Linq.XDocument.Load")]
    [InlineData("class C { object Read() => JsonDocument.Parse(\"x\"); }", "System.Text.Json.JsonDocument.Parse")]
    [InlineData("class C { object Read() => typeof(File).GetMethod(\"ReadAllText\"); }", "System.Reflection:System.IO.File")]
    [InlineData("class C { object Read() { var type = typeof(File); return type.GetMethod(\"ReadAllText\"); } }", "System.Reflection:System.IO.File")]
    [InlineData("class C { string Read() => global::System.IO.File.ReadAllText(\"x\"); }", "System.IO.File.ReadAllText")]
    [InlineData("class C { object Read() => new DirectoryInfo(AppContext.BaseDirectory).Parent; }", "System.AppContext.BaseDirectory")]
    [InlineData("class C { string Read() => Helper(); string Helper() => File.ReadAllText(\"x\"); }", "System.IO.File.ReadAllText")]
    public void DirectRepositoryIoShapesAreRejected(string source, string expectedApi)
    {
        var finding = Assert.Single(RepositoryIoAccessPolicy.InspectSource("Sample.cs", source));

        Assert.Equal(expectedApi, finding.Api);
    }

    [Fact]
    public void TypedRepositoryAccessorUseIsAccepted()
    {
        const string source = "class C { string Read(RepositoryAccessor repository) => repository.ReadAllText(RepositoryRelativePath.Create(\"x\")); }";

        Assert.Empty(RepositoryIoAccessPolicy.InspectSource("Sample.cs", source));
    }

    [Fact]
    public void UnrecognizedIoAliasFailsClosed()
    {
        const string source = "using F = System.IO.File; class C { string Read() => F.ReadAllText(\"x\"); }";

        var finding = Assert.Single(RepositoryIoAccessPolicy.InspectSource("Sample.cs", source));

        Assert.Equal("UNRECOGNIZED", finding.Api);
    }

    [Fact]
    public void ForbiddenTemporaryGatewayMemberIsRejected()
    {
        const string source = "static class TemporaryFileSystem { static object Escape(string path) => System.IO.File.OpenRead(path); }";

        var finding = Assert.Single(RepositoryIoAccessPolicy.InspectSource(
            RepositoryIoAccessPolicy.TemporaryFileSystemPath,
            source));

        Assert.Equal("System.IO.File.OpenRead", finding.Api);
    }

    [Fact]
    public void UnrecognizedSyntaxFailsClosed()
    {
        var findings = RepositoryIoAccessPolicy.InspectSource("Sample.cs", "class C { string Read( => File.ReadAllText(\"x\"); }");

        Assert.Contains(findings, static finding => finding.Api == "UNRECOGNIZED");
    }
}
