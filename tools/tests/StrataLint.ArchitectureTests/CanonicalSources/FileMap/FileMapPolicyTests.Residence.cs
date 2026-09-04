using StrataLint.Engine;
using StrataLint.Cli;

namespace StrataLint.ArchitectureTests;

public sealed partial class FileMapPolicyTests
{
    [Theory]
    [InlineData("ledger", false)]
    [InlineData("data", true)]
    public void AcceptedLedgerDirectoryRequiresLedgerEntries(string kind, bool hasFinding)
    {
        var path = FrozenLedgerChangeClassifier.AcceptedPath(
            "sha256:" + new string('a', 64));
        var manifest = Parse(Entry(path, kind, "FrozenLedgerCanonicalWriter", "FrozenLedger", "SL-008"));

        var findings = FileMapPolicy.InspectDirectoryKinds(manifest, [path]);

        Assert.Equal(hasFinding, findings.Any(
            static finding => finding.Code == "FILEMAP-DIRECTORY-KIND"));
    }

    [Theory]
    [InlineData("data", false)]
    [InlineData("ledger", true)]
    public void FrozenStateDirectoryRequiresDataEntries(string kind, bool hasFinding)
    {
        const string path = "Golden/Frozen/state/D5/S0/Carrier/Ring.lean.json";
        var manifest = Parse(Entry(path, kind, "FrozenStateWriter", "FrozenStateCatalog", "SL-008"));

        var findings = FileMapPolicy.InspectDirectoryKinds(manifest, [path]);

        Assert.Equal(hasFinding, findings.Any(
            static finding => finding.Code == "FILEMAP-DIRECTORY-KIND"));
    }

    [Fact]
    public void ExactProtectedResidenceCountIsAccepted()
    {
        const string path = "tools/FixtureData/known.toml";
        var manifest = Parse(1, ResidenceEntry(path));

        Assert.Empty(FileMapPolicy.InspectDirectoryKinds(manifest, [path]));
    }

    [Fact]
    public void AdditionalProtectedResidenceViolationIsRejected()
    {
        var manifest = Parse(
            1,
            ResidenceEntry("tools/FixtureData/*.toml"));

        var finding = Assert.Single(FileMapPolicy.InspectDirectoryKinds(
            manifest,
            [
                "tools/FixtureData/known.toml",
                "tools/FixtureData/new.toml",
            ]));

        Assert.Equal("FILEMAP-RESIDENCE-DRIFT", finding.Code);
    }

    [Fact]
    public void MissingProtectedResidenceViolationIsRejected()
    {
        const string path = "tools/FixtureData/known.toml";
        var manifest = Parse(2, ResidenceEntry(path));

        var finding = Assert.Single(FileMapPolicy.InspectDirectoryKinds(manifest, [path]));

        Assert.Equal("FILEMAP-RESIDENCE-DRIFT", finding.Code);
    }

    [Fact]
    public void ResidenceInventoryIncludesOnlyMarkedProtectedData()
    {
        const string externalPath = "Data/known.toml";
        const string unmarkedPath = "tools/FixtureData/other.toml";
        const string markedPath = "tools/FixtureData/values.toml";
        var manifest = Parse(
            ResidenceEntry(externalPath),
            Entry(unmarkedPath, "data", "none", "reader", "SnapshotDecoder"),
            ResidenceEntry(markedPath));

        var violations = FileMapPolicy.ResidenceViolations(
            manifest,
            [externalPath, markedPath, unmarkedPath]);

        Assert.Equal([markedPath], violations);
    }
}
