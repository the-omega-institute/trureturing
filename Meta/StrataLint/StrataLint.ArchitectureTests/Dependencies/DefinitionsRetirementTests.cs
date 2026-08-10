namespace StrataLint.ArchitectureTests;

public sealed class DefinitionsRetirementTests
{
    private static readonly string RetiredAssemblyName = "StrataLint." + "Definitions";
    private static readonly string RetiredRoot =
        "Meta/StrataLint/" + RetiredAssemblyName;
    private const string GoldenCorpusPath =
        "Meta/StrataLint/StrataLint.Cli/Golden/GoldenCorpus.cs";
    private const string TomlGoldenLoaderPath =
        "Meta/StrataLint/StrataLint.Cli/Golden/TomlGoldenLoader.cs";
    private const string TomlGoldenWriterPath =
        "Meta/StrataLint/StrataLint.Cli/Golden/TomlGoldenWriter.cs";
    private const string AnchorPath =
        "Meta/StrataLint/StrataLint.Engine/Anchors/Anchor.cs";
    private const string AnchorDefinitionPath =
        "Meta/StrataLint/StrataLint.Engine/Anchors/AnchorDefinition.cs";
    private const string AnchorSchemesPath =
        "Meta/StrataLint/StrataLint.Engine/Anchors/AnchorSchemes.cs";
    private const string AnchorCatalogDefinitionsPath =
        "Meta/StrataLint/StrataLint.Engine/Anchors/AnchorCatalogDefinitions.cs";
    private const string ExternalAnchorManifestPath =
        "Meta/StrataLint/StrataLint.Engine/Anchors/ExternalAnchorManifest.cs";
    private const string SolutionPath = "Meta/StrataLint/StrataLint.sln";
    private const string CliProjectPath =
        "Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj";
    private const string ScribeProjectPath =
        "Meta/StrataLint/StrataLint.Scribe/StrataLint.Scribe.csproj";
    private const string TestsProjectPath =
        "Meta/StrataLint/StrataLint.Tests/StrataLint.Tests.csproj";
    private const string ScribeTestsProjectPath =
        "Meta/StrataLint/StrataLint.Scribe.Tests/StrataLint.Scribe.Tests.csproj";
    private const string ArchitectureTestsProjectPath =
        "Meta/StrataLint/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj";

    public static TheoryData<string> FinalSourceOwners => new()
    {
        GoldenCorpusPath,
        TomlGoldenLoaderPath,
        TomlGoldenWriterPath,
        AnchorPath,
        AnchorDefinitionPath,
        AnchorSchemesPath,
        AnchorCatalogDefinitionsPath,
        ExternalAnchorManifestPath,
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
            "Meta",
            "StrataLint",
            "StrataLint.Scribe",
            "Values",
            "ValuesKernelDataLoader.cs")));
    }
}
