namespace StrataLint.ArchitectureTests;

/// <summary>
/// Keeps compile metadata on the registered FILEMAP/manifest path.  Runtime MSBuild
/// reference discovery was an accidental second source of truth and must not return.
/// </summary>
public sealed class RegisteredMetadataPolicyTests
{
    [Fact]
    public void CompileMetadataDoesNotDiscoverOrTransportUnregisteredReferences()
    {
        var root = RepositoryLayout.FindRoot();
        var source = File.ReadAllText(Path.Combine(
            root,
            "tools/StrataLint.EngineeringScope/CommonCompileMetadata.cs"));

        Assert.DoesNotContain("QueryReferencePaths", source, StringComparison.Ordinal);
        Assert.DoesNotContain("getItem:Reference", source, StringComparison.Ordinal);
        Assert.DoesNotContain("HintPath", source, StringComparison.Ordinal);
        Assert.DoesNotContain("MsBuildCompileOracle", source, StringComparison.Ordinal);
    }
}
