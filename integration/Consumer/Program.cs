using Trureturing.Truth;

// Downstream consumer side of the branch-CI publish proof. This program depends ONLY on the
// published Trureturing.Truth NuGet package (restored, locked, from the runner-local feed) and on a
// published truth-release.v1 bundle directory downloaded as a CI artifact. It does NOT check out this
// repository and does NOT synthesize a bundle: it verifies and reads the bytes it was handed, which
// is exactly what a downstream paper/pages consumer does with an upstream daily release.
// Usage: Consumer <published-bundle-directory>.
if (args.Length != 1 || string.IsNullOrWhiteSpace(args[0]))
{
    Console.Error.WriteLine("usage: Consumer <published-bundle-directory>");
    return 2;
}

var bundleDirectory = Path.GetFullPath(args[0]);
var digestPath = Path.Combine(bundleDirectory, "RELEASE_DIGEST");
if (!Directory.Exists(bundleDirectory) || !File.Exists(digestPath))
{
    Console.Error.WriteLine($"TRUTH RELEASE V2 CONSUME FAILED: no published bundle at {bundleDirectory}");
    return 1;
}

const string truthPath = "D5/S0/IntegrationTruth.lean";
const string sourceCommit = "1111111111111111111111111111111111111111";
const string sourceTree = "2222222222222222222222222222222222222222";
var expectedReleaseDigest = File.ReadAllText(digestPath).Trim();

try
{
    // The whole downstream contract, entirely through the package's public surface:
    // out-of-band digest -> fail-closed verification -> typed, verified reads.
    var verified = TruthReleaseVerification.Verify(bundleDirectory, expectedReleaseDigest);
    var verifiedGraph = verified.ReadTruthGraph();
    var verifiedExport = verified.ReadTruthExport();

    if (verified.ReleaseDigest != expectedReleaseDigest
        || verifiedGraph.Schema != TruthGraphExportModel.Dialect
        || verifiedGraph.Truth.Nodes.Length != 1
        || verifiedGraph.Truth.Nodes[0].RepoPath != truthPath
        || verifiedExport.Dialect != TruthExportModel.CanonicalDialect
        || verifiedExport.SourceCommit != sourceCommit
        || verifiedExport.SourceTree != sourceTree
        || verifiedExport.Nodes.Length != 1
        || verifiedExport.Nodes[0].RepoPath != truthPath)
    {
        throw new InvalidOperationException("Verified typed release contents did not match the published bundle.");
    }

    Console.WriteLine(
        $"TRUTH RELEASE V2 CONSUME OK release={verified.ReleaseDigest} "
        + $"graph_nodes={verifiedGraph.Truth.Nodes.Length} export_nodes={verifiedExport.Nodes.Length} "
        + $"source_commit={verified.Manifest.Source.SourceCommit} source_repo={verified.Manifest.Source.SourceRepo}");
    return 0;
}
catch (Exception exception)
{
    Console.Error.WriteLine($"TRUTH RELEASE V2 CONSUME FAILED: {exception}");
    return 1;
}
