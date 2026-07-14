using System.Text.Json;
using StrataLint.Scribe;

namespace StrataLint.Scribe.Tests;

public sealed class AnchorCatalogTests
{
    [Fact]
    public void ExternalManifestIsTheCatalogEntryPoint()
    {
        var definition = Assert.Single(ExternalAnchorManifest.All);

        Assert.IsType<MathlibAnchor>(definition.Anchor);
    }

    [Fact]
    public void CatalogHasUniqueExternalMembers()
    {
        var definitions = AnchorCatalogDefinitions.All;

        Assert.Single(definitions);
        Assert.Equal(
            definitions.Length,
            definitions.Select(static item => item.Anchor.CanonicalString)
                .Distinct(StringComparer.Ordinal)
                .Count());
        Assert.All(definitions, static definition =>
        {
            Assert.True(definition.Anchor is LiteratureAnchor or MathlibAnchor);
            var parsed = Assert.IsType<AnchorParseResult.Parsed>(
                Anchor.TryParseCanonical(definition.Anchor.CanonicalString)).Value;
            Assert.Equal(definition.Anchor, parsed);
        });
    }

    [Fact]
    public void CatalogProjectionContainsNoCompatibilityTable()
    {
        using var document = JsonDocument.Parse(CanonicalAnchorCatalogWriter.Write().ToArray());

        Assert.Equal(
            ["definitions", "schema_version"],
            document.RootElement.EnumerateObject().Select(static property => property.Name));
    }

    [Fact]
    public void ExternalCatalogEntryCarriesPinnedProvenance()
    {
        using var document = JsonDocument.Parse(CanonicalAnchorCatalogWriter.Write().ToArray());
        var definition = Assert.Single(
            document.RootElement.GetProperty("definitions").EnumerateArray());

        Assert.Equal(
            ["anchor", "provenance"],
            definition.EnumerateObject().Select(static property => property.Name));
        Assert.Equal(
            "mathlib revision fabf563a7c95a166b8d7b6efca11c8b4dc9d911f; reference locator module Mathlib.Data.Nat.Fib.Zeckendorf",
            definition.GetProperty("provenance").GetString());
    }

    [Fact]
    public void CatalogWriterIsByteStableAndMatchesTheCommittedProjection()
    {
        var first = CanonicalAnchorCatalogWriter.Write();
        var second = CanonicalAnchorCatalogWriter.Write();
        var committed = File.ReadAllBytes(Path.Combine(
            FindRepositoryRoot(),
            CanonicalAnchorCatalogWriter.RelativePath));

        Assert.True(first.AsSpan().SequenceEqual(second.AsSpan()));
        Assert.True(first.AsSpan().SequenceEqual(committed));
        Assert.Equal((byte)'\n', first[^1]);
    }

    [Fact]
    public void CatalogEmitterWritesAndChecksTheExactProjection()
    {
        var root = Path.Combine(Path.GetTempPath(), "stratalint-catalog-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(root);
        try
        {
            using var output = new StringWriter();
            using var error = new StringWriter();

            Assert.Equal(0, AnchorCatalogEmitter.Emit(root, check: false, output, error));
            Assert.Equal(0, AnchorCatalogEmitter.Emit(root, check: true, output, error));
            Assert.Equal(string.Empty, error.ToString());

            var path = Path.Combine(root, CanonicalAnchorCatalogWriter.RelativePath);
            File.AppendAllText(path, " ");

            Assert.Equal(1, AnchorCatalogEmitter.Emit(root, check: true, output, error));
            Assert.Contains("out of date", error.ToString(), StringComparison.Ordinal);
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "Meta", "BACKFILL.yaml")))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}
