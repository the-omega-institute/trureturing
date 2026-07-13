using System.Collections.Immutable;
using StrataLint.Scribe;

namespace StrataLint.Scribe.Tests;

public sealed class AnchorCatalogTests
{
    [Fact]
    public void TheoryManifestCanBeTheFirstCatalogEntryPoint()
    {
        var definitions = TheoryAnchorManifest.All;

        Assert.Equal(14, definitions.Length);
    }

    [Fact]
    public void CatalogIsACanonicalTargetBijection()
    {
        var definitions = AnchorCatalogDefinitions.All;

        Assert.Equal(27, definitions.Length);
        Assert.Equal(
            definitions.Length,
            definitions.Select(static item => item.Anchor.CanonicalString)
                .Distinct(StringComparer.Ordinal)
                .Count());
        Assert.Equal(
            definitions.Length,
            definitions.Select(static item => item.Target.SemanticKey)
                .Distinct(StringComparer.Ordinal)
                .Count());
        Assert.All(definitions, static definition =>
        {
            var parsed = Assert.IsType<AnchorParseResult.Parsed>(
                Anchor.TryParseCanonical(definition.Anchor.CanonicalString)).Value;
            Assert.Equal(definition.Anchor, parsed);
        });
    }

    [Fact]
    public void CatalogProjectionContainsNoCompatibilityTable()
    {
        using var document = System.Text.Json.JsonDocument.Parse(
            CanonicalAnchorCatalogWriter.Write().ToArray());

        Assert.Equal(
            ["definitions", "schema_version"],
            document.RootElement.EnumerateObject().Select(static property => property.Name));
    }

    [Fact]
    public void GictSevenFifteenResolvesToTheThreeDistanceSourceNode()
    {
        var definition = Assert.Single(AnchorCatalogDefinitions.All, static item =>
            item.Anchor.CanonicalString == "gict/v3.6/VII.7/theorem/7.15");

        Assert.Equal("gict:v3.6:VII.7:theorem:7.15", definition.Target.SemanticKey);
        Assert.Equal("## VII.7 ", definition.Target.Selector.HeadingPrefix);
        Assert.Equal("**定理 7.15(", definition.Target.Selector.LinePrefix);
        Assert.IsType<AnchorResolution.Resolved>(
            AnchorResolver.Resolve(definition.Anchor, FindRepositoryRoot()));
    }

    [Theory]
    [InlineData("sos1957threegap")]
    [InlineData("paleywiener1934fourier")]
    public void LiteratureWithoutALocalLibraryTargetIsUnregistered(string bibKey)
    {
        Assert.DoesNotContain(AnchorCatalogDefinitions.All, item =>
            item.Anchor.CanonicalString == "lit/" + bibKey);
        Assert.IsType<AnchorResolution.Unregistered>(
            AnchorResolver.Resolve(Anchor.ParseCanonical("lit/" + bibKey), FindRepositoryRoot()));
    }

    [Fact]
    public void MathlibTargetStaysRegisteredOpenWithoutAnExternalReceipt()
    {
        var resolution = AnchorResolver.Resolve(
            AnchorCatalogDefinitions.MathlibZeckendorfModule,
            FindRepositoryRoot());

        var open = Assert.IsType<AnchorResolution.RegisteredOpen>(resolution);
        Assert.Equal("D5-T0016", open.CaseId);
        Assert.Equal(
            "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f",
            open.Receipt.SourceRevision);
    }

    [Theory]
    [InlineData("{\"packages\":[{\"name\":\"mathlib\",\"rev\":17}]}\n")]
    [InlineData("[]\n")]
    [InlineData("{\"packages\":[17]}\n")]
    public void MalformedMathlibPinIsAnInvalidTarget(string manifest)
    {
        var root = Path.Combine(Path.GetTempPath(), "stratalint-anchor-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(root);
        File.WriteAllText(Path.Combine(root, "lake-manifest.json"), manifest);

        try
        {
            var resolution = AnchorResolver.Resolve(
                AnchorCatalogDefinitions.MathlibZeckendorfModule,
                root);

            Assert.IsType<AnchorResolution.InvalidTarget>(resolution);
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void EveryResolvedLocalDefinitionResolvesAgainstTheRepository()
    {
        var root = FindRepositoryRoot();
        var local = AnchorCatalogDefinitions.All
            .Where(static item => item.Status == AnchorRegistrationStatus.Resolved)
            .ToArray();

        Assert.Equal(26, local.Length);
        Assert.All(local, definition =>
        {
            var resolved = Assert.IsType<AnchorResolution.Resolved>(
                AnchorResolver.Resolve(definition.Anchor, root));
            Assert.Equal(definition.Target.SemanticKey, resolved.Target.SemanticKey);
            Assert.Equal(definition.Target.SourcePath, resolved.Receipt.SourcePath);
        });
    }

    [Fact]
    public void FrozenSourceHashDriftIsInvalidTarget()
    {
        var root = FindRepositoryRoot();
        var temporary = Path.Combine(Path.GetTempPath(), "stratalint-anchor-" + Guid.NewGuid().ToString("N"));
        var source = Assert.IsType<TheoryNodeTarget>(
            AnchorCatalogDefinitions.GictI1Definition1_1Definition.Target);
        var destination = Path.Combine(temporary, source.SourcePath);
        Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
        File.WriteAllText(
            destination,
            File.ReadAllText(Path.Combine(root, source.SourcePath)) + "\nsource drift\n");
        var backfill = Path.Combine(temporary, "Meta", "BACKFILL.yaml");
        Directory.CreateDirectory(Path.GetDirectoryName(backfill)!);
        File.Copy(Path.Combine(root, "Meta", "BACKFILL.yaml"), backfill);

        try
        {
            var resolution = AnchorResolver.Resolve(
                AnchorCatalogDefinitions.GictI1Definition1_1,
                temporary);

            var invalid = Assert.IsType<AnchorResolution.InvalidTarget>(resolution);
            Assert.Contains("SHA-256", invalid.Reason, StringComparison.Ordinal);
        }
        finally
        {
            Directory.Delete(temporary, recursive: true);
        }
    }

    [Fact]
    public void TheorySourceIdMustMatchTheBackfillSourcePath()
    {
        var root = FindRepositoryRoot();
        var temporary = Path.Combine(Path.GetTempPath(), "stratalint-anchor-" + Guid.NewGuid().ToString("N"));
        var source = Assert.IsType<TheoryNodeTarget>(
            AnchorCatalogDefinitions.GictI1Definition1_1Definition.Target);
        var destination = Path.Combine(temporary, source.SourcePath);
        Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
        File.Copy(Path.Combine(root, source.SourcePath), destination);
        var backfill = Path.Combine(temporary, "Meta", "BACKFILL.yaml");
        Directory.CreateDirectory(Path.GetDirectoryName(backfill)!);
        File.WriteAllText(
            backfill,
            File.ReadAllText(Path.Combine(root, "Meta", "BACKFILL.yaml"))
                .Replace(source.SourcePath, "docs/develop/theory/wrong.md", StringComparison.Ordinal));

        try
        {
            var resolution = AnchorResolver.Resolve(
                AnchorCatalogDefinitions.GictI1Definition1_1,
                temporary);

            var invalid = Assert.IsType<AnchorResolution.InvalidTarget>(resolution);
            Assert.Contains("BACKFILL", invalid.Reason, StringComparison.Ordinal);
        }
        finally
        {
            Directory.Delete(temporary, recursive: true);
        }
    }

    [Fact]
    public void GictDefinitionCannotResolveUnderTheWrongDivision()
    {
        var actual = Assert.IsType<TheoryNodeTarget>(
            AnchorCatalogDefinitions.All.Single(static definition =>
                definition.Anchor.CanonicalString == "gict/v3.6/I.2/definition/1.4").Target);
        var wrongDefinition = new AnchorDefinition(
            Anchor.ParseCanonical("gict/v3.6/I.1/definition/1.4"),
            new TheoryNodeTarget(
                "gict:v3.6:I.1:definition:1.4",
                actual.SourceId,
                actual.SourcePath,
                actual.SourceRevision,
                actual.ExpectedSha256!,
                actual.Selector),
            AnchorRegistrationStatus.Resolved);
        var resolveLocal = typeof(AnchorResolver).GetMethod(
            "ResolveLocal",
            System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Static);

        var resolution = Assert.IsAssignableFrom<AnchorResolution>(
            resolveLocal!.Invoke(null, [wrongDefinition, FindRepositoryRoot()]));

        var invalid = Assert.IsType<AnchorResolution.InvalidTarget>(resolution);
        Assert.Contains("division", invalid.Reason, StringComparison.Ordinal);
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
