namespace StrataLint.ArchitectureTests;

public sealed class DefinitionsRetirementTests
{
    private static readonly string RetiredAssemblyName = "StrataLint." + "Definitions";
    private static readonly string RetiredRoot =
        "tools/" + RetiredAssemblyName;
    private const string AnchorPath =
        "tools/StrataLint.Engine/Anchors/Anchor.cs";
    private const string AnchorSchemesPath =
        "tools/StrataLint.Engine/Anchors/AnchorSchemes.cs";
    private const string SolutionPath = "tools/StrataLint.sln";
    private const string CliProjectPath =
        "tools/StrataLint.Cli/StrataLint.Cli.csproj";
    private const string ScribeProjectPath =
        "tools/StrataLint.Scribe/StrataLint.Scribe.csproj";
    private const string TestsProjectPath =
        "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj";
    private const string ScribeTestsProjectPath =
        "tools/tests/StrataLint.Scribe.Tests/StrataLint.Scribe.Tests.csproj";
    private const string ArchitectureTestsProjectPath =
        "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj";

    public static TheoryData<string> FinalSourceOwners => new()
    {
        AnchorPath,
        AnchorSchemesPath,
    };

    public static TheoryData<string> ProjectAndSolutionFiles => new()
    {
        SolutionPath,
        CliProjectPath,
        ScribeProjectPath,
        TestsProjectPath,
        ScribeTestsProjectPath,
        ArchitectureTestsProjectPath,
    };

    [Fact]
    public void DefinitionsAssemblyIsRetired()
    {
        var root = RepositoryLayout.FindRoot();

        Assert.False(Directory.Exists(Path.Combine(root, RetiredRoot)));
    }

    [Theory]
    [MemberData(nameof(FinalSourceOwners))]
    public void DefinitionSourceHasAFinalProgramOwner(string path)
    {
        Assert.True(File.Exists(Path.Combine(RepositoryLayout.FindRoot(), path)), path);
    }

    [Theory]
    [MemberData(nameof(ProjectAndSolutionFiles))]
    public void BuildGraphDoesNotReferenceTheRetiredAssembly(string path)
    {
        var source = File.ReadAllText(Path.Combine(RepositoryLayout.FindRoot(), path));

        Assert.DoesNotContain(RetiredAssemblyName, source, StringComparison.Ordinal);
    }

    [Fact]
    public void ValuesTruthAndComputationDataRemainOutsideAssemblies()
    {
        var root = RepositoryLayout.FindRoot();

        Assert.True(File.Exists(Path.Combine(root, "D5", "S3", "Constants", "Values.lean")));
        Assert.True(File.Exists(Path.Combine(root, "Golden", "values-kernels.toml")));
        Assert.True(File.Exists(Path.Combine(
            root,
            "tools", "StrataLint.Scribe",
            "Values",
            "ValuesKernelDataLoader.cs")));
    }
}
