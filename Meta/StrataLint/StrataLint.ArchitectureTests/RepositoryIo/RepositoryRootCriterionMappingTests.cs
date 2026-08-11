namespace StrataLint.ArchitectureTests;

public sealed class RepositoryRootCriterionMappingTests
{
    private static readonly IReadOnlyDictionary<string, string> HistoricalCriteria =
        new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["AnchorCatalogTests.cs"] = "GlobalJsonAndBlueprintDirectoryNotFound",
            ["Census/CensusDerivationTests.cs"] = "GlobalJsonAndBlueprintDirectoryNotFound",
            ["Describe/DescribeMigrationTests.cs"] = "GlobalJsonAndBlueprintDirectoryNotFound,GlobalJsonAndBlueprintDirectoryNotFound",
            ["Describe/FormulaCorpusInventoryTests.cs"] = "ClaudeDirectoryNotFound",
            ["Describe/Quantum/ChannelFixedStateDocumentTests.cs"] = "ClaudeDirectoryNotFound",
            ["EmissionTests.cs"] = "GlobalJsonAndBlueprintInvalidOperation,GlobalJsonAndBlueprintInvalidOperation,GlobalJsonAndBlueprintInvalidOperation,GlobalJsonAndBlueprintInvalidOperation,GlobalJsonAndBlueprintInvalidOperation,GlobalJsonAndBlueprintInvalidOperation,GlobalJsonAndBlueprintInvalidOperation",
            ["FileMap/FileMapEmitterTests.cs"] = "FileMapDirectoryNotFound",
            ["FileMap/FileMapManifestTests.cs"] = "FileMapDirectoryNotFound",
            ["PdfWriterTests.cs"] = "GlobalJsonAndLibraryInvalidOperation",
            ["PilotDocumentTests.cs"] = "GlobalJsonAndBlueprintDirectoryNotFound,GlobalJsonAndBlueprintDirectoryNotFound,GlobalJsonAndBlueprintDirectoryNotFound",
            ["Projection/StatementProjectionPilotTests.cs"] = "LakefileInvalidOperation,LakefileInvalidOperation,LakefileInvalidOperation,LakefileInvalidOperation,LakefileInvalidOperation",
            ["Support/RepositoryAccessorTests.cs"] = "GlobalJsonAndBlueprintDirectoryNotFound,LakefileInvalidOperation,ClaudeDirectoryNotFound,ClaudeDirectoryNotFound,ClaudeDirectoryNotFound,ClaudeDirectoryNotFound",
            ["V3/LeanCompiledArtifactReportsTests.cs"] = "ClaudeDirectoryNotFound",
            ["Values/ValuesDefinitionTests.cs"] = "ValuesDataDirectoryNotFound,ValuesDataDirectoryNotFound",
            ["Values/ValuesProjectionTests.cs"] = "ValuesProducerDirectoryNotFound,ValuesProducerDirectoryNotFound,ValuesProducerDirectoryNotFound,ValuesProducerDirectoryNotFound,ValuesProducerDirectoryNotFound",
        };

    [Fact]
    public void EveryRepositoryRootCallSiteKeepsItsHistoricalCriterion()
    {
        var findings = RepositoryRootCriterionMappingPolicy.InspectRepository(
            RepositoryLayout.FindRoot(),
            HistoricalCriteria);

        Assert.Empty(findings);
    }

    [Fact]
    public void LegalButWrongCriterionIsRejected()
    {
        const string source = "class C { void M() => RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound); }";

        var findings = RepositoryRootCriterionMappingPolicy.InspectSource(
            "Values/ValuesDefinitionTests.cs",
            source,
            HistoricalCriteria);

        Assert.Single(findings);
    }
}
