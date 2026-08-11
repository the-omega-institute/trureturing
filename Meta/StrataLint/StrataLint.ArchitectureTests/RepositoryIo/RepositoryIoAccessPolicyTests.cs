namespace StrataLint.ArchitectureTests;

public sealed class RepositoryIoAccessPolicyTests
{
    [Fact]
    public void ScribeTestsRepositoryIoIsConfinedToNamedGateways()
    {
        var findings = RepositoryIoAccessPolicy.InspectRepository(RepositoryLayout.FindRoot());

        Assert.True(findings.Count == 0, string.Join(Environment.NewLine, findings));
    }

    [Theory]
    [InlineData("class C { string Read() => File.ReadAllText(\"x\"); }", "System.IO.File.ReadAllText")]
    [InlineData("class C { object Read() => Directory.EnumerateFiles(\"x\"); }", "System.IO.Directory.EnumerateFiles")]
    [InlineData("class C { object Read() => new FileStream(\"x\", FileMode.Open); }", "System.IO.FileStream")]
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
}
