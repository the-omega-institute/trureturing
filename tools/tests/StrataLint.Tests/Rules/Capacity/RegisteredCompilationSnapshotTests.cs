using StrataLint.Engine;
using StrataLint.TestSupport;

namespace StrataLint.Tests;

public sealed class RegisteredCompilationSnapshotTests
{
    [Fact]
    public void SnapshotKeepsRegisteredIdentityAndRawSourceContent()
    {
        const string source = "\uFEFF// raw bytes \t\r\nclass Deep {}\r\n \t";
        var files = Files(source);
        var context = ScribeProjectCompilationContext.Create(files, EngineeringProjectRegistry.Read(files));
        var project = Assert.Single(context.Projects);
        Assert.Equal("Explicit", project.AssemblyName);
        Assert.Equal(source, Assert.Single(project.Sources).Content);
        Assert.Equal("deep/nested/Source.cs", Assert.Single(project.Sources).Path);
    }

    [Fact]
    public void SnapshotReadsDeclaredInputsWithoutCreatingACheckout()
    {
        var files = Files("class Deep {}");
        // Valid snapshot paths can collide as filesystem file/directory names. Consuming bytes
        // needs no checkout, MSBuild or project execution to establish declared membership.
        files = [.. files, new("deep/nested/Source.cs/Child.cs", "class Child {}")];
        var context = ScribeProjectCompilationContext.Create(files, EngineeringProjectRegistry.Read(files));
        Assert.Equal(2, Assert.Single(context.Projects).Sources.Count);
    }

    [Fact]
    public void MetadataCompileIncludesDoNotInventSourceOwnership()
    {
        var files = Files("class Deep {}");
        files = [.. files, new("other/Unregistered.cs", "class Other {}")];
        Assert.Throws<InvalidDataException>(() =>
            ScribeProjectCompilationContext.Create(files, EngineeringProjectRegistry.Read(files)));
    }

    [Fact]
    public void RegisteredSourceProjectionIsIndependentOfNonSourceData()
    {
        var files = Files("class Deep {}");
        var before = ScribeProjectCompilationContext.Create(files, EngineeringProjectRegistry.Read(files));
        files = [.. files, new("notes.txt", "not a compiler input")];
        var after = ScribeProjectCompilationContext.Create(files, EngineeringProjectRegistry.Read(files));
        Assert.Equal(Assert.Single(before.Projects).Sources, Assert.Single(after.Projects).Sources);
    }

    private static ScribeTrackedSource[] Files(string source) =>
    [
        new(EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Manifest(
            new EngineeringProjectFixture("p/project.csproj", "Explicit", "test-support", false, ["deep/**/*.cs"]))),
        new("p/project.csproj", "<Project><PropertyGroup><AssemblyName>Wrong</AssemblyName></PropertyGroup><ItemGroup><Compile Include=\"../other/*.cs\" /></ItemGroup></Project>"),
        new("deep/nested/Source.cs", source),
    ];
}
