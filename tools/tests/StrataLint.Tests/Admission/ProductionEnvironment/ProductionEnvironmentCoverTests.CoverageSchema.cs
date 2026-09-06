using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void CoverAtomWritesCoverageGidsEntryAsObjectEdge()
    {
        var inputs = DirectoryInputs(CoverWorld.Materialize(new CoverSpec()));
        var atom = Assert.Single(inputs.Files, pair =>
            pair.Key.EndsWith(CoverWorld.DefaultAtomId + ".yaml", StringComparison.Ordinal));
        Assert.Contains("coverage_gids: []", atom.Value, StringComparison.Ordinal);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.CoverAtom(CoverArgs(inputs));

        Assert.True(result.Success, result.Error);
        var writtenPath = Path.Combine(
            temporary.Path,
            BackfillInventoryLoader.RootPath.Replace('/', Path.DirectorySeparatorChar),
            "fixture-source",
            "absorbed-closed",
            CoverWorld.DefaultAtomId + ".yaml");
        var written = File.ReadAllText(writtenPath);
        Assert.Contains(
            "coverage_gids:\n  - gid: D5/S0/Carrier/Probe.probe\n    target_statement_id: sha256:",
            written,
            StringComparison.Ordinal);
        Assert.DoesNotContain("\ncoverage:\n", written, StringComparison.Ordinal);
    }
}
