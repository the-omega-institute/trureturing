using System.Text;
using StrataLint.Cli;
using StrataLint.Scribe;
using StrataLint.Tests;

namespace StrataLint.ArchitectureTests;

// A run-local generated set is a projection: the producer owns it and nothing reads it from the
// index. FILEMAP is the authority and the tree must obey, so a declared run-local member that is
// tracked is a finding against the tree, never a reason to redeclare the entry.
public sealed class FileMapRunLocalTrackingTests
{
    private const string TrackedMessage =
        "run-local artifact must be removed from the Git index; "
        + "the FILEMAP declaration must not be changed to make this finding go away";

    [Fact]
    public void TrackedDataKeyedRunLocalMemberMustBeRemovedFromTheIndex()
    {
        const string path = "Generated/partitions/source-a.md";

        var finding = Assert.Single(FileMapPolicy.InspectGeneratedInventory(
            Parse(DataKeyedRunLocalEntry),
            [path],
            []));

        Assert.Equal("FILEMAP-RUN-LOCAL-TRACKED", finding.Code);
        Assert.Equal(path, finding.Path);
        Assert.Equal(TrackedMessage, finding.Message);
    }

    [Fact]
    public void UntrackedDataKeyedRunLocalSetHasNoTrackedFinding()
    {
        var findings = FileMapPolicy.InspectGeneratedInventory(
            Parse(DataKeyedRunLocalEntry),
            ["Generated/unrelated.md"],
            []);

        Assert.DoesNotContain(findings, static finding =>
            finding.Code == "FILEMAP-RUN-LOCAL-TRACKED");
    }

    [Fact]
    public void TrackedDataKeyedCommittedSourceSetHasNoRunLocalFinding()
    {
        var findings = FileMapPolicy.InspectGeneratedInventory(
            Parse(DataKeyedCommittedSourceEntry),
            ["Blueprint/D5/S0/Carrier/Synthetic.md"],
            []);

        Assert.DoesNotContain(findings, static finding =>
            finding.Code == "FILEMAP-RUN-LOCAL-TRACKED");
    }

    private const string DataKeyedRunLocalEntry = """
        [[files]]
        pattern = "Generated/partitions/*.md"
        kind = "generated"
        admission_plane = "content"
        produced_by = "PartitionEmitter"
        consumed_by = ["reader"]
        verified_by = ["PartitionEmitter"]
        artifact_id = "none"
        runtime_disposition = "run-local"

        """;

    private const string DataKeyedCommittedSourceEntry = """
        [[files]]
        pattern = "Blueprint/**/*.md"
        kind = "generated"
        admission_plane = "content"
        produced_by = "ScribeEmitter"
        consumed_by = ["reader"]
        verified_by = ["ScribeEmitter"]
        artifact_id = "none"
        runtime_disposition = "committed-source"

        """;

    private static FileMapManifest Parse(string entry) =>
        FileMapLoader.Parse(
            Encoding.UTF8.GetBytes(
                """
                schema_version = 2

                [residence_policy]
                case_id = "RESIDENCE-EPOCH"
                desired = "data-must-live-outside-tools"
                known_violation_count = 0
                status = "known-violations-frozen-under-monitoring"

                """ + entry),
            "fixture.toml");
}
