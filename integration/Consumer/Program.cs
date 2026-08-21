using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using Trureturing.Truth;

// A downstream consumer that touches ONLY the package's public API: it builds a release bundle with the
// canonical writers, verifies it, and reads the typed truth graph + frozen export back through the logical
// accessors. It never opens a manifest filename itself. This is the publish -> consume proof at a real
// NuGet package boundary.

static string Hex(byte[] bytes) => Convert.ToHexStringLower(SHA256.HashData(bytes));
var utf8 = new UTF8Encoding(false);
const string commit = "1111111111111111111111111111111111111111";
const string tree = "2222222222222222222222222222222222222222";

var truthGraph = TruthGraphJsonWriter.Write(new TruthGraphExportModel(
    TruthGraphExportModel.Dialect,
    1,
    new TruthGraphProvenance("sha256:aa", "sha256:bb") { TruthRootSha256 = "sha256:cc", DependencyGranularity = "module-import" },
    new TruthGraphSection(
        ImmutableArray<TruthGraphNode>.Empty,
        ImmutableArray<TruthGraphEdge>.Empty,
        ImmutableArray<TruthGraphOpenBlocker>.Empty,
        new TruthGraphStateCounts(0, 0, 0, 0)),
    new DocumentGraphSection(
        ImmutableArray<DocumentGraphNode>.Empty,
        ImmutableArray<DescribeGraphNode>.Empty,
        ImmutableArray<DocumentDependencyEdge>.Empty,
        ImmutableArray<DocumentNarrativeReferenceEdge>.Empty),
    new TruthGraphJoinsSection(ImmutableArray<TruthAnchorJoin>.Empty),
    ImmutableArray.Create("digestion"))).ToArray();

var truthExport = TruthExportJsonWriter.Write(TruthExportModel.Create(
    ImmutableArray.Create(new TruthExportNode(
        "D5/S0/A.lean",
        "sha256:fa",
        ImmutableArray.Create("propext"),
        ImmutableArray.Create(new TruthExportDeclaration("nk-a", "theorem", "sha256:a")))),
    commit,
    tree)).ToArray();

var artifacts = new (string Key, string File, byte[] Bytes)[]
{
    ("source_snapshot", "source-snapshot.v1.json", utf8.GetBytes("source_snapshot")),
    ("truth_graph", "truth-graph.v1.json", truthGraph),
    ("raw_lean_report", "raw-lean-report.json", utf8.GetBytes("raw_lean_report")),
    ("truth_export", "truth-export.v1.json", truthExport),
    ("blueprint_index", "blueprint-index.v1.json", utf8.GetBytes("blueprint_index")),
    ("frozen_ledger_head", "frozen-ledger-head.json", utf8.GetBytes("frozen_ledger_head")),
    ("residual_frontier", "echo-residual-summary.md", utf8.GetBytes("residual_frontier")),
};

var sums = string.Concat(artifacts
    .OrderBy(a => a.File, StringComparer.Ordinal)
    .Select(a => Hex(a.Bytes) + "  " + a.File + "\n"));
var digest = "sha256:" + Convert.ToHexStringLower(SHA256.HashData(utf8.GetBytes(sums)));
var artifactJson = string.Join(",\n", artifacts.Select(a =>
    $"    \"{a.Key}\": {{ \"file\": \"{a.File}\", \"sha256\": \"sha256:{Hex(a.Bytes)}\" }}"));
var manifest = $@"{{
  ""schema"": ""truth-release.v1"",
  ""source"": {{ ""source_repo"": ""the-omega-institute/trureturing"", ""source_commit"": ""{commit}"", ""source_tree"": ""{tree}"" }},
  ""trust"": {{
    ""commit_on_protected_dev"": true,
    ""required_checks"": [
      {{ ""name"": ""Candidate harness engineering checks"", ""conclusion"": ""success"" }},
      {{ ""name"": ""Canonical Lean report production"", ""conclusion"": ""success"" }},
      {{ ""name"": ""Content-addressed dev baseline admission"", ""conclusion"": ""success"" }}
    ]
  }},
  ""producer"": {{ ""package_repo"": ""the-omega-institute/trureturing-fkst-packages"", ""package_commit"": ""3333333333333333333333333333333333333333"", ""read_only"": true }},
  ""artifacts"": {{
{artifactJson}
  }},
  ""sha256sums_digest"": ""{digest}"",
  ""produced_at"": ""2026-08-21T00:00:00Z""
}}";

var dir = Directory.CreateTempSubdirectory("consume").FullName;
foreach (var artifact in artifacts)
{
    File.WriteAllBytes(Path.Combine(dir, artifact.File), artifact.Bytes);
}

File.WriteAllText(Path.Combine(dir, "SHA256SUMS"), sums, utf8);
File.WriteAllText(Path.Combine(dir, "release-manifest.v1.json"), manifest, utf8);

try
{
    var verified = TruthReleaseVerification.Verify(dir, digest);
    var graph = verified.ReadTruthGraph();
    var export = verified.ReadTruthExport();

    if (graph.Schema != TruthGraphExportModel.Dialect || export.Dialect != "stratalint.truth-export.v1"
        || export.Nodes.Length != 1 || export.Nodes[0].RepoPath != "D5/S0/A.lean")
    {
        Console.Error.WriteLine("CONSUME FAILED: unexpected typed models");
        return 1;
    }

    Console.WriteLine(
        $"CONSUME OK  release={verified.ReleaseDigest}  graph.schema={graph.Schema}  " +
        $"export.dialect={export.Dialect}  export.nodes={export.Nodes.Length}  firstNode={export.Nodes[0].RepoPath}  " +
        $"firstDecl={export.Nodes[0].Declarations[0].DeclarationNameKey}");
    return 0;
}
finally
{
    Directory.Delete(dir, recursive: true);
}
