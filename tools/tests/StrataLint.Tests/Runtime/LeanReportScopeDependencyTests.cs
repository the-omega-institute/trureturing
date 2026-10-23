using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LeanReportScopeDependencyTests
{
    private const string BridgePath = "tools/lean-inspector-interface/LocalBridge/Catalog.lean";
    private const string Registration = """
        {"schema_version":1,"dependency_sources":{"include":[
          {"pattern":"tools/lean-inspector-interface/**/*.lean","optional":false}
        ],"exclude":[]}}
        """;

    [Fact]
    public void TraversesRegisteredInterfaceAndReportsOnlyManagedModules()
    {
        var scope = LeanReportScope.Create(Snapshot(), [RepoPath.CreateKnown("D5/Selected.lean")]);

        Assert.Equal(["D5/Dependency.lean", "D5/Selected.lean"],
            scope.Paths.Select(path => path.Value).Order(StringComparer.Ordinal));
        Assert.DoesNotContain(RepoPath.CreateKnown(BridgePath), scope.Paths);
        Assert.DoesNotContain(RepoPath.CreateKnown("D5/Sibling.lean"), scope.Paths);
    }

    [Fact]
    public void RejectsMissingManagedDependencyBehindTheInterface()
    {
        Assert.Throws<InvalidOperationException>(() => LeanReportScope.Create(
            Snapshot(bridge: "prelude\nimport D5.Missing\n"),
            [RepoPath.CreateKnown("D5/Selected.lean")]));
    }

    [Fact]
    public void RequiresFilesForNonoptionalDependencyRegistration()
    {
        Assert.Throws<InvalidDataException>(() => LeanReportScope.Create(
            Snapshot(includeBridge: false), [RepoPath.CreateKnown("D5/Selected.lean")]));
    }

    [Theory]
    [InlineData("{\"schema_version\":1}")]
    [InlineData("{\"dependency_sources\":{\"include\":[],\"exclude\":[]}}")]
    [InlineData("{\"dependency_sources\":{\"include\":[{\"pattern\":\"tools/**/*.lean\",\"optional\":true}],\"exclude\":[\"tools/**\"]}}")]
    public void UnregisteredOrExcludedInterfaceCannotEnlargeScope(string registration)
    {
        var scope = LeanReportScope.Create(Snapshot(registration), [RepoPath.CreateKnown("D5/Selected.lean")]);
        Assert.Equal("D5/Selected.lean", Assert.Single(scope.Paths).Value);
    }

    [Theory]
    [InlineData("{\"dependency_sources\":null}")]
    [InlineData("{\"dependency_sources\":{\"include\":[],\"exclude\":[],\"extra\":true}}")]
    [InlineData("{\"dependency_sources\":{\"include\":[{\"pattern\":\"../**/*.lean\",\"optional\":true}],\"exclude\":[]}}")]
    [InlineData("{\"dependency_sources\":{\"include\":[],\"include\":[],\"exclude\":[]}}")]
    public void InvalidDependencyRegistrationIsRejected(string registration)
    {
        Assert.Throws<InvalidDataException>(() => LeanReportScope.Create(
            Snapshot(registration), [RepoPath.CreateKnown("D5/Selected.lean")]));
    }

    [Fact]
    public void ReportCannotOmitTheManagedDescendantOfARegisteredInterface()
    {
        var snapshot = Snapshot();
        var selectedSnapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create([RawRepositoryEntry.FromText("D5/Selected.lean",
                "prelude\nimport LocalBridge.Catalog\n")]))).Snapshot;
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            ["D5/Selected.lean"] = new(["LocalBridge.Catalog"], []),
        });
        var bytes = Encoding.UTF8.GetBytes(Encoding.UTF8.GetString(
            RawLeanReportArtifact.Write(selectedSnapshot, report).AsSpan()).Replace(
                RawLeanReportArtifact.Schema, RawLeanReportArtifact.ScopedSchema, StringComparison.Ordinal));
        var scope = LeanReportScope.Create(snapshot, [RepoPath.CreateKnown("D5/Selected.lean")]);

        var exception = Assert.Throws<FormatException>(() => RawLeanReportArtifact.ReadForScope(bytes, scope));
        Assert.Contains("D5/Dependency.lean", exception.Message, StringComparison.Ordinal);
    }

    private static RepositorySnapshot Snapshot(string registration = Registration,
        string bridge = "prelude\nimport D5.Dependency\n", bool includeBridge = true)
    {
        var entries = new List<RawRepositoryEntry>
        {
            RawRepositoryEntry.FromText("lean-report-inputs.json", registration),
            RawRepositoryEntry.FromText("D5/Selected.lean", "prelude\nimport LocalBridge.Catalog\n"),
            RawRepositoryEntry.FromText("D5/Dependency.lean", "prelude\n"),
            RawRepositoryEntry.FromText("D5/Sibling.lean", "prelude\n"),
        };
        if (includeBridge) entries.Add(RawRepositoryEntry.FromText(BridgePath, bridge));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(entries))).Snapshot;
    }
}
