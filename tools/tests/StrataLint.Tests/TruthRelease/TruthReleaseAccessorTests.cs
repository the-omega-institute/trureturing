using System;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using System.Text;
using Trureturing.Truth;
using Xunit;

namespace StrataLint.Tests;

public sealed class TruthReleaseAccessorTests
{
    private static readonly UTF8Encoding Utf8 = new(false, true);
    private const string Commit = "1111111111111111111111111111111111111111";
    private const string Tree = "2222222222222222222222222222222222222222";

    private static string Hex(byte[] bytes) => Convert.ToHexStringLower(SHA256.HashData(bytes));

    // A minimal but strictly valid truth graph (empty sets + the one required deferred layer). Written
    // through the canonical writer so the reader's round-trip byte check accepts it.
    private static byte[] MinimalTruthGraphBytes() =>
        TruthGraphJsonWriter.Write(new TruthGraphExportModel(
            TruthGraphExportModel.Dialect,
            1,
            new TruthGraphProvenance("sha256:aa", "sha256:bb")
            {
                TruthRootSha256 = "sha256:cc",
                DependencyGranularity = "module-import",
            },
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

    private static byte[] TruthExportBytes() =>
        TruthExportJsonWriter.Write(TruthExportModel.Create(
            ImmutableArray.Create(new TruthExportNode(
                "D5/S0/A.lean",
                "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                ImmutableArray.Create("propext"),
                ImmutableArray.Create(new TruthExportDeclaration(
                    "nk-a",
                    "theorem",
                    "sha256:1111111111111111111111111111111111111111111111111111111111111111")),
                ImmutableArray<string>.Empty)),
            Commit,
            Tree)).ToArray();

    // Assemble a self-consistent bundle from real content and return its directory + release digest.
    private static (string Directory, string Digest) BuildBundle(byte[] truthGraph, byte[] truthExport)
    {
        var artifacts = new (string Key, string File, byte[] Bytes)[]
        {
            ("source_snapshot", "source-snapshot.v1.json", Utf8.GetBytes("source_snapshot")),
            ("truth_graph", "truth-graph.v1.json", truthGraph),
            ("raw_lean_report", "raw-lean-report.json", Utf8.GetBytes("raw_lean_report")),
            ("truth_export", "truth-export.v1.json", truthExport),
            ("blueprint_index", "blueprint-index.v1.json", Utf8.GetBytes("blueprint_index")),
            ("frozen_ledger_head", "frozen-ledger-head.json", Utf8.GetBytes("frozen_ledger_head")),
            ("residual_frontier", "echo-residual-summary.md", Utf8.GetBytes("residual_frontier")),
        };

        var sums = string.Concat(artifacts
            .OrderBy(static a => a.File, StringComparer.Ordinal)
            .Select(static a => Hex(a.Bytes) + "  " + a.File + "\n"));
        var digest = "sha256:" + Convert.ToHexStringLower(SHA256.HashData(new UTF8Encoding(false).GetBytes(sums)));

        var artifactJson = string.Join(",\n", artifacts.Select(a =>
            $"    \"{a.Key}\": {{ \"file\": \"{a.File}\", \"sha256\": \"sha256:{Hex(a.Bytes)}\" }}"));
        var manifest = $@"{{
  ""schema"": ""truth-release.v1"",
  ""source"": {{ ""source_repo"": ""the-omega-institute/trureturing"", ""source_commit"": ""{Commit}"", ""source_tree"": ""{Tree}"" }},
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

        var directory = Directory.CreateTempSubdirectory("truthaccess").FullName;
        foreach (var artifact in artifacts)
        {
            File.WriteAllBytes(Path.Combine(directory, artifact.File), artifact.Bytes);
        }

        File.WriteAllText(Path.Combine(directory, "SHA256SUMS"), sums, new UTF8Encoding(false));
        File.WriteAllText(Path.Combine(directory, "release-manifest.v1.json"), manifest, new UTF8Encoding(false));
        return (directory, digest);
    }

    [Fact]
    public void LogicalAccessorsReturnTheVerifiedTypedModels()
    {
        var (directory, digest) = BuildBundle(MinimalTruthGraphBytes(), TruthExportBytes());
        try
        {
            var verified = TruthReleaseVerification.Verify(directory, digest);

            var graph = verified.ReadTruthGraph();
            Assert.Equal(TruthGraphExportModel.Dialect, graph.Schema);
            Assert.Empty(graph.Truth.Nodes);

            var export = verified.ReadTruthExport();
            Assert.Equal("stratalint.truth-export.v1", export.Dialect);
            Assert.Equal("D5/S0/A.lean", Assert.Single(export.Nodes).RepoPath);
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [Fact]
    public void AnAccessorRejectsBytesChangedAfterVerification()
    {
        var (directory, digest) = BuildBundle(MinimalTruthGraphBytes(), TruthExportBytes());
        try
        {
            var verified = TruthReleaseVerification.Verify(directory, digest);

            // Tamper the artifact on disk AFTER verification; the accessor rereads, rehashes, and refuses,
            // so holding a VerifiedTruthRelease never yields post-verification bytes (verify/use TOCTOU).
            File.WriteAllText(Path.Combine(directory, "truth-graph.v1.json"), "tampered", new UTF8Encoding(false));
            Assert.Throws<FormatException>(() => verified.ReadTruthGraph());
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }
}
