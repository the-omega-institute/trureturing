using StrataLint.Cli;
using StrataLint.Scribe;

namespace StrataLint.ArchitectureTests;

public sealed partial class FileMapPolicyTests
{
    [Theory]
    [InlineData("run-local", false)]
    [InlineData("committed-source", true)]
    public void UntrackedGeneratedInventoryRespectsRuntimeDisposition(
        string runtimeDisposition,
        bool expectsStaleFinding)
    {
        var manifest = Parse(DispositionEntry(
            "Generated/output.json",
            "generated",
            "JsonEmitter",
            "reader",
            "JsonEmitter",
            runtimeDisposition,
            "A-OUTPUT"));
        var inventory = new GeneratedArtifactIdentity(
            "Generated/output.json", "JsonEmitter", "A-OUTPUT");

        var findings = FileMapPolicy.InspectGeneratedInventory(manifest, [], [inventory]);

        Assert.Equal(
            expectsStaleFinding,
            findings.Any(static finding => finding.Code == "FILEMAP-GENERATED-STALE-INVENTORY"));
    }

    [Fact]
    public void TrackedRunLocalGeneratedArtifactMustBeRemovedFromTheIndex()
    {
        const string artifactPath = "SyntheticArtifacts/output.json";
        var manifest = Parse(DispositionEntry(
            artifactPath, "generated", "SyntheticEmitter", "reader", "SyntheticEmitter",
            "run-local", "A-SYNTHETIC-OUTPUT"));
        var inventory = new GeneratedArtifactIdentity(
            artifactPath, "SyntheticEmitter", "A-SYNTHETIC-OUTPUT");

        var finding = Assert.Single(FileMapPolicy.InspectGeneratedInventory(
            manifest, [artifactPath], [inventory]));

        Assert.Equal("FILEMAP-RUN-LOCAL-TRACKED", finding.Code);
        Assert.Contains("remove", finding.Message, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("index", finding.Message, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("must not be changed", finding.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Theory]
    [InlineData("run-local", false)]
    [InlineData("committed-source", true)]
    public void ValidGeneratedDispositionDoesNotProduceDispositionFinding(
        string runtimeDisposition,
        bool isTracked)
    {
        const string artifactPath = "SyntheticArtifacts/output.json";
        var manifest = Parse(DispositionEntry(
            artifactPath, "generated", "SyntheticEmitter", "reader", "SyntheticEmitter",
            runtimeDisposition, "A-SYNTHETIC-OUTPUT"));
        var inventory = new GeneratedArtifactIdentity(
            artifactPath, "SyntheticEmitter", "A-SYNTHETIC-OUTPUT");
        var trackedPaths = isTracked ? new[] { artifactPath } : [];

        var findings = FileMapPolicy.InspectGeneratedInventory(manifest, trackedPaths, [inventory]);

        Assert.DoesNotContain(findings, static finding =>
            finding.Code is "FILEMAP-GENERATED-DISPOSITION" or "FILEMAP-RUN-LOCAL-TRACKED");
    }

    [Fact]
    public void UntrackedRunLocalWithWrongProducerIsRejectedByTheRedFixture()
    {
        var manifest = Parse(DispositionEntry(
            "Generated/output.json", "generated", "WrongEmitter", "reader", "WrongEmitter",
            "run-local", "A-OUTPUT"));
        var inventory = new GeneratedArtifactIdentity(
            "Generated/output.json", "JsonEmitter", "A-OUTPUT");

        var findings = FileMapPolicy.InspectGeneratedInventory(manifest, [], [inventory]);

        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-GENERATED-PRODUCER");
        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-GENERATED-STALE-INVENTORY");
    }

    [Fact]
    public void UntrackedRunLocalWithBroadGlobIsRejectedByTheRedFixture()
    {
        var manifest = Parse(DispositionEntry(
            "Generated/*.json", "generated", "JsonEmitter", "reader", "JsonEmitter",
            "run-local", "A-OUTPUT"));
        var inventory = new GeneratedArtifactIdentity(
            "Generated/output.json", "JsonEmitter", "A-OUTPUT");

        var findings = FileMapPolicy.InspectGeneratedInventory(manifest, [], [inventory]);

        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-GENERATED-LITERAL");
        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-GENERATED-STALE-INVENTORY");
    }

    [Fact]
    public void RunLocalEntryMissingRequiredFieldIsRejectedByTheRedFixture()
    {
        var source = DispositionEntry(
            "Generated/output.json", "generated", "JsonEmitter", "reader", "JsonEmitter",
            "run-local", "A-OUTPUT").Replace("mode = \"100644\"\n", string.Empty, StringComparison.Ordinal);

        var exception = Assert.Throws<FormatException>(() => Parse(source));

        Assert.Contains("mode", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CommittedGeneratedEntryMissingModeIsRejectedByTheRedFixture()
    {
        var source = DispositionEntry(
            "Generated/output.json", "generated", "JsonEmitter", "reader", "JsonEmitter",
            "committed-source", "A-OUTPUT").Replace("mode = \"100644\"\n", string.Empty, StringComparison.Ordinal);

        var exception = Assert.Throws<FormatException>(() => Parse(source));

        Assert.Contains("mode", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void WrongDeclaredCommittedModeIsRejectedByTheRedFixture()
    {
        var manifest = Parse(DispositionEntry(
            "Generated/output.json", "generated", "JsonEmitter", "reader", "JsonEmitter",
            "committed-source", "A-OUTPUT").Replace("100644", "100755", StringComparison.Ordinal));

        var finding = Assert.Single(FileMapPolicy.InspectDeclaredModes(
            manifest,
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["Generated/output.json"] = "100644",
            }));

        Assert.Equal("FILEMAP-GENERATED-MODE", finding.Code);
    }
}
