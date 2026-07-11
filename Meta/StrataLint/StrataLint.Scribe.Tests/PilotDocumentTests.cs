using StrataLint.Scribe.Definitions;

namespace StrataLint.Scribe.Tests;

public sealed class PilotDocumentTests
{
    [Fact]
    public void PilotCatalogHasExactlyTheThreeAdjudicatedBlueprints()
    {
        Assert.Equal(
            [
                "D5/S1/Phase/Basic",
                "D5/S1/Scale/Embedding",
                "D5/S1/Scale/Log",
            ],
            PilotDocuments.All.Select(static item => item.Document.Header.Gid.Value));
        Assert.Equal(
            [
                "Blueprint/D5/S1/Phase/Basic.md",
                "Blueprint/D5/S1/Scale/Embedding.md",
                "Blueprint/D5/S1/Scale/Log.md",
            ],
            PilotDocuments.All.Select(static item => item.RelativePath.Value));
    }

    [Fact]
    public void PilotMarkdownIsDeterministicAndMatchesTheCommittedTree()
    {
        var repositoryRoot = FindRepositoryRoot();

        foreach (var pilot in PilotDocuments.All)
        {
            var first = CanonicalMarkdownWriter.Write(pilot.Document);
            var second = CanonicalMarkdownWriter.Write(pilot.Document);
            var committed = File.ReadAllBytes(
                Path.Combine(repositoryRoot, pilot.RelativePath.Value));

            Assert.Equal(first.ToArray(), second.ToArray());
            Assert.Equal(committed, first.ToArray());
        }
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "global.json"))
                && Directory.Exists(Path.Combine(current.FullName, "Blueprint")))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException("Could not locate the repository root.");
    }
}
