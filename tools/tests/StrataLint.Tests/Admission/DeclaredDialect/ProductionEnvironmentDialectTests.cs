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
            WithProbeDialect(fixture.Files[TheoryAtomizerDataLoader.DataPath]);
        var rules = TheoryAtomizerDataLoader.Load(fixture.Build().Current);
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, oldBytes, rules).Claims);
        Assert.Equal("proposition/1.1", oldAtom.AstPath);

        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        fixture.Baseline[TheoryAtomizerDataLoader.DataPath] =
            fixture.Files[TheoryAtomizerDataLoader.DataPath];
        InstallDirectoryLedger(fixture, atomizerId, oldAtom);
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        // Atomised, not degraded: a fallback here would mean the dialect never resolved.
        Assert.Contains("coarse_fallbacks=0", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("INGEST_INCOMPLETE", result.Output, StringComparison.Ordinal);
        var written = BackfillInventoryLoader.LoadRoot(temporary.Path);
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
            WithProbeDialect(fixture.Files[TheoryAtomizerDataLoader.DataPath]);
        var rules = TheoryAtomizerDataLoader.Load(fixture.Build().Current);

        var error = Assert.Throws<FormatException>(() => AtomizerRegistry.Atomize(
            "dialect:absent-volume",
            Encoding.UTF8.GetBytes("# 探针\n\n**命题 1.1(甲)**。x。\n"),
            rules));

        Assert.Contains("absent-volume", error.Message, StringComparison.Ordinal);
        Assert.Contains(ProbeDialectId, error.Message, StringComparison.Ordinal);
    }

    private const string DialectDeclaration = """
        [[dialect]]
        id = "probe-dialect"
        claim = "^\\*\\*(?<kind>\\p{L}+)\\s*(?<number>[0-9]+(?:\\.[0-9]+)+)"
        """;

    private const string DialectGenres = """
        [[dialect.genre]]
        dialect = "probe-dialect"
        token = "命题"
        kind = "proposition"

        [[dialect.genre]]
        dialect = "probe-dialect"
        token = "观察"
        kind = "observation"
        """;

    /// <summary>
    /// Splices the probe dialect into atomizer data that may already declare dialects of
    /// its own: sections are ordered, so the declaration must join the [[dialect]] block
    /// rather than trail the genres.
    /// </summary>
    private static string WithProbeDialect(string data)
    {
        var genres = data.IndexOf("[[dialect.genre]]", StringComparison.Ordinal);
        var withDeclaration = genres < 0
            ? data.TrimEnd('\n') + "\n\n" + DialectDeclaration + "\n\n" + DialectGenres + "\n"
            : data[..genres] + DialectDeclaration + "\n\n" + data[genres..];
        var suffixes = withDeclaration.IndexOf("[[dialect.genre_suffix]]", StringComparison.Ordinal);
        return suffixes < 0 || genres < 0
            ? withDeclaration
            : withDeclaration[..suffixes] + DialectGenres + "\n\n" + withDeclaration[suffixes..];
    }
}
