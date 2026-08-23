using System.Collections.Immutable;
using System.Text;
using Trureturing.Truth;

const string sourceCommit = "1111111111111111111111111111111111111111";
const string sourceTree = "2222222222222222222222222222222222222222";
const string packageCommit = "3333333333333333333333333333333333333333";
const string truthPath = "D5/S0/IntegrationTruth.lean";

static ImmutableArray<byte> Utf8(string value) =>
    ImmutableArray.CreateRange(new UTF8Encoding(false).GetBytes(value));

static string Digest(ImmutableArray<byte> bytes) =>
    "sha256:" + Sha256Sums.HashHex(bytes.AsSpan());

var rawLeanReportBytes = Utf8("{\"modules\":[],\"schema\":\"stratalint-raw-lean-report-v1\"}\n");
var blueprintIndexBytes = Utf8("{\"blueprints\":[]}\n");
var frozenLedgerHeadBytes = Utf8("{\"event_count\":1,\"head\":\"integration-v2\"}\n");
var residualFrontierBytes = Utf8("# Residual frontier\n\nNo open integration blockers.\n");

var truthGraph = new TruthGraphExportModel(
    TruthGraphExportModel.Dialect,
    1,
    new TruthGraphProvenance(
        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        Digest(rawLeanReportBytes))
    {
        TruthRootSha256 = "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
        DependencyGranularity = "module-import",
    },
    new TruthGraphSection(
        ImmutableArray.Create(new TruthGraphNode(
            truthPath,
            "D5.S0.IntegrationTruth",
            "closed",
            "D5.S0.IntegrationTruth",
            0)),
        ImmutableArray<TruthGraphEdge>.Empty,
        ImmutableArray<TruthGraphOpenBlocker>.Empty,
        new TruthGraphStateCounts(1, 0, 0, 0)),
    new DocumentGraphSection([], [], [], []),
    new TruthGraphJoinsSection([]),
    ["digestion"]);
var truthGraphBytes = TruthGraphJsonWriter.Write(truthGraph);

var truthExport = TruthExportModel.Create(
    ImmutableArray.Create(new TruthExportNode(
        truthPath,
        "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
        ImmutableArray.Create("propext"),
        ImmutableArray.Create(new TruthExportDeclaration(
            "integration.truth",
            "theorem",
            "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd")),
        ImmutableArray<string>.Empty)),
    sourceCommit,
    sourceTree);
var truthExportBytes = TruthExportJsonWriter.Write(truthExport);

var sourceSnapshot = new SourceSnapshotModel(
    "source-snapshot.v1",
    "the-omega-institute/trureturing",
    sourceCommit,
    sourceTree,
    "leanprover/lean4:v4.31.0",
    "4444444444444444444444444444444444444444",
    packageCommit,
    Digest(truthGraphBytes),
    Digest(rawLeanReportBytes),
    Digest(Utf8("# Truth DAG\n")),
    Digest(residualFrontierBytes),
    Digest(truthExportBytes),
    Digest(frozenLedgerHeadBytes),
    1);
var source = new TruthReleaseSource(
    "the-omega-institute/trureturing",
    sourceCommit,
    sourceTree);
var trust = new TruthReleaseTrust(
    CommitOnProtectedDev: true,
    ImmutableArray.Create(
        new TruthReleaseRequiredCheck("Candidate harness engineering checks", "success"),
        new TruthReleaseRequiredCheck("Canonical Lean report production", "success"),
        new TruthReleaseRequiredCheck("Content-addressed dev baseline admission", "success")),
    BlessedBy: null);
var producer = new TruthReleaseProducer(
    "the-omega-institute/trureturing",
    packageCommit,
    ReadOnly: true);

var bundleDirectory = Directory.CreateTempSubdirectory("truth-release-v2-consumer").FullName;
try
{
    var input = new TruthReleaseBundleInput(
        sourceSnapshot,
        truthGraphBytes,
        rawLeanReportBytes,
        truthExportBytes,
        blueprintIndexBytes,
        frozenLedgerHeadBytes,
        residualFrontierBytes,
        source,
        trust,
        producer,
        "2026-08-23T00:00:00Z");
    var releaseDigest = TruthReleaseBundleWriter.WriteBundle(bundleDirectory, input);
    var verified = TruthReleaseVerification.Verify(bundleDirectory, releaseDigest);
    var verifiedGraph = verified.ReadTruthGraph();
    var verifiedExport = verified.ReadTruthExport();

    if (verifiedGraph.Schema != TruthGraphExportModel.Dialect
        || verifiedGraph.Truth.Nodes.Length != 1
        || verifiedGraph.Truth.Nodes[0].RepoPath != truthPath
        || verifiedExport.Dialect != TruthExportModel.CanonicalDialect
        || verifiedExport.SourceCommit != sourceCommit
        || verifiedExport.SourceTree != sourceTree
        || verifiedExport.Nodes.Length != 1
        || verifiedExport.Nodes[0].RepoPath != truthPath)
    {
        throw new InvalidOperationException("Verified typed release contents did not match the coherent inputs.");
    }

    Console.WriteLine(
        $"TRUTH RELEASE V2 INTEGRATION OK release={verified.ReleaseDigest} "
        + $"graph_nodes={verifiedGraph.Truth.Nodes.Length} export_nodes={verifiedExport.Nodes.Length} "
        + $"source_commit={verified.Manifest.Source.SourceCommit}");
    return 0;
}
catch (Exception exception)
{
    Console.Error.WriteLine($"TRUTH RELEASE V2 INTEGRATION FAILED: {exception}");
    return 1;
}
finally
{
    Directory.Delete(bundleDirectory, recursive: true);
}
