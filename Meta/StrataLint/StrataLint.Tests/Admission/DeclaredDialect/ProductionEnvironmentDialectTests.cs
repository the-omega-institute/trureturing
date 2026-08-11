using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

/// <summary>
/// The acceptance condition for a declared dialect, exercised through the ingest command
/// rather than through the atomizer alone: a document plus configuration digests a volume.
///
/// This runs end to end on purpose. Unit coverage of AtomizerRegistry.Atomize passed while
/// ingest still refused `dialect:` ids, because the ingest path also resolves an atomizer
/// through AtomizerRegistry.Require for its residual stem. Only the whole command exercises
/// both.
/// </summary>
public sealed partial class ProductionEnvironmentTests
{
    private const string ProbeDialectId = "probe-dialect";

    [Fact]
    public void IngestDigestsAVolumeWhoseDialectIsOnlyDeclaredInData()
    {
        var fixture = new RuleFixture();
        var atomizerId = "dialect:" + ProbeDialectId;
        var oldBytes = Encoding.UTF8.GetBytes("# 探针\n\n**命题 1.1(甲)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# 探针\n\n**命题 1.1(甲)**。old。\n\n**观察 2.3.4(乙)**。new。\n");
        fixture.Files[TheoryAtomizerDataLoader.DataPath] =
            fixture.Files[TheoryAtomizerDataLoader.DataPath].TrimEnd('\n') + "\n\n" + DeclaredDialect;
        var rules = TheoryAtomizerDataLoader.Load(fixture.Build().Current);
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, oldBytes, rules).Claims);
        Assert.Equal("proposition/1.1", oldAtom.AstPath);

        var ledger = IngestLedger(atomizerId, oldAtom);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        fixture.Baseline[TheoryAtomizerDataLoader.DataPath] =
            fixture.Files[TheoryAtomizerDataLoader.DataPath];
        InstallLedger(fixture, ledger, oldAtom);
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, ledger, new UTF8Encoding(false));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.Ingest(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        // Atomised, not degraded: a fallback here would mean the dialect never resolved.
        Assert.Contains("coarse_fallbacks=0", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("INGEST_INCOMPLETE", result.Output, StringComparison.Ordinal);
        var written = BackfillInventoryLoader.Load(File.ReadAllText(outputPath));
        var source = Assert.Single(written.RequireDigestionSources());
        Assert.Equal(atomizerId, source.Atomizer);
        Assert.Contains(
            source.Entries,
            entry => entry.AstPath == "observation/2.3.4");
    }

    /// <summary>A declared dialect is refused before use when its id resolves to nothing.</summary>
    [Fact]
    public void IngestRefusesASourceNamingAnUndeclaredDialect()
    {
        var fixture = new RuleFixture();
        fixture.Files[TheoryAtomizerDataLoader.DataPath] =
            fixture.Files[TheoryAtomizerDataLoader.DataPath].TrimEnd('\n') + "\n\n" + DeclaredDialect;
        var rules = TheoryAtomizerDataLoader.Load(fixture.Build().Current);

        var error = Assert.Throws<FormatException>(() => AtomizerRegistry.Atomize(
            "dialect:absent-volume",
            Encoding.UTF8.GetBytes("# 探针\n\n**命题 1.1(甲)**。x。\n"),
            rules));

        Assert.Contains("absent-volume", error.Message, StringComparison.Ordinal);
        Assert.Contains(ProbeDialectId, error.Message, StringComparison.Ordinal);
    }

    private const string DeclaredDialect = """
        [[dialect]]
        id = "probe-dialect"
        claim = "^\\*\\*(?<kind>\\p{L}+)\\s*(?<number>[0-9]+(?:\\.[0-9]+)+)"

        [[dialect.genre]]
        dialect = "probe-dialect"
        token = "命题"
        kind = "proposition"

        [[dialect.genre]]
        dialect = "probe-dialect"
        token = "观察"
        kind = "observation"
        """;
}
