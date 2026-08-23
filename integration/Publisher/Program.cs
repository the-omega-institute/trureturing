using System.Collections.Immutable;
using System.Text;
using Trureturing.Truth;

// Publisher side of the branch-CI publish proof. This stands in for the upstream producer: it
// assembles a coherent truth-release.v1 bundle (the seven artifacts, including truth-graph.v1.json
// — the DAG — plus SHA256SUMS and release-manifest.v1.json) into the output directory and records
// the release digest next to it. A separate consumer job then restores only the published NuGet
// package and this published bundle directory, with no checkout of this repository, and verifies
// and reads it. Usage: Publisher <output-bundle-directory>.
if (args.Length != 1 || string.IsNullOrWhiteSpace(args[0]))
{
    Console.Error.WriteLine("usage: Publisher <output-bundle-directory>");
    return 2;
}

var bundleDirectory = Path.GetFullPath(args[0]);
Directory.CreateDirectory(bundleDirectory);

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
File.WriteAllText(
    Path.Combine(bundleDirectory, "RELEASE_DIGEST"),
    releaseDigest + "\n",
    new UTF8Encoding(false));

Console.WriteLine(
    $"PUBLISHED truth-release.v1 bundle to {bundleDirectory} release={releaseDigest} "
    + $"(dag=truth-graph.v1.json)");
return 0;
