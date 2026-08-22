using System;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using System.Text;
using Trureturing.Truth;
using Xunit;

namespace StrataLint.Tests;

public sealed class TruthReleaseVerificationTests
{
    private static readonly UTF8Encoding Utf8 = new(false, true);
    private const string Commit = "1111111111111111111111111111111111111111";
    private const string OtherCommit = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    private const string Tree = "2222222222222222222222222222222222222222";
    private const string OtherTree = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";

    private static string Digest(byte[] bytes) =>
        "sha256:" + Convert.ToHexStringLower(SHA256.HashData(bytes));

    private static byte[] MinimalTruthGraphBytes(string contentDigest = "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa") =>
        TruthGraphJsonWriter.Write(new TruthGraphExportModel(
            TruthGraphExportModel.Dialect,
            1,
            new TruthGraphProvenance(
                contentDigest,
                "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb")
            {
                TruthRootSha256 = "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
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

    private static byte[] TruthExportBytes(string commit, string tree) =>
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
            commit,
            tree)).ToArray();

    private static byte[] SourceSnapshotBytes(string commit, string tree, string truthGraphDigest) =>
        Utf8.GetBytes($$"""
            {
              "schema": "source-snapshot.v1",
              "source_repo": "the-omega-institute/trureturing",
              "source_commit": "{{commit}}",
              "source_tree": "{{tree}}",
              "lean_toolchain": "leanprover/lean4:v4.24.0",
              "mathlib_rev": "3333333333333333333333333333333333333333",
              "producer_package_commit": "4444444444444444444444444444444444444444",
              "truth_graph_sha256": "{{truthGraphDigest}}",
              "raw_lean_report_sha256": "sha256:5555555555555555555555555555555555555555555555555555555555555555",
              "dag_md_sha256": "sha256:6666666666666666666666666666666666666666666666666666666666666666",
              "residual_frontier_sha256": "sha256:7777777777777777777777777777777777777777777777777777777777777777",
              "declarations_sha256": "sha256:8888888888888888888888888888888888888888888888888888888888888888",
              "frozen_ledger_head_hash": "sha256:9999999999999999999999999999999999999999999999999999999999999999",
              "frozen_ledger_sequence": 42
            }
            """);

    private static (string Directory, string Digest) BuildBundle(
        string snapshotCommit = Commit,
        string exportCommit = Commit,
        string manifestCommit = Commit,
        string snapshotTree = Tree,
        string exportTree = Tree,
        string manifestTree = Tree,
        string? snapshotTruthGraphDigest = null,
        byte[]? truthGraph = null,
        byte[]? truthExport = null)
    {
        truthGraph ??= MinimalTruthGraphBytes();
        truthExport ??= TruthExportBytes(exportCommit, exportTree);
        var sourceSnapshot = SourceSnapshotBytes(
            snapshotCommit,
            snapshotTree,
            snapshotTruthGraphDigest ?? Digest(truthGraph));
        var artifacts = new (string Key, string File, byte[] Bytes)[]
        {
            ("source_snapshot", "source-snapshot.v1.json", sourceSnapshot),
            ("truth_graph", "truth-graph.v1.json", truthGraph),
            ("raw_lean_report", "raw-lean-report.json", Utf8.GetBytes("raw_lean_report")),
            ("truth_export", "truth-export.v1.json", truthExport),
            ("blueprint_index", "blueprint-index.v1.json", Utf8.GetBytes("blueprint_index")),
            ("frozen_ledger_head", "frozen-ledger-head.json", Utf8.GetBytes("frozen_ledger_head")),
            ("residual_frontier", "echo-residual-summary.md", Utf8.GetBytes("residual_frontier")),
        };

        var sums = string.Concat(artifacts
            .OrderBy(static artifact => artifact.File, StringComparer.Ordinal)
            .Select(artifact => Digest(artifact.Bytes)["sha256:".Length..] + "  " + artifact.File + "\n"));
        var releaseDigest = Digest(Utf8.GetBytes(sums));
        var artifactJson = string.Join(",\n", artifacts.Select(artifact =>
            $"    \"{artifact.Key}\": {{ \"file\": \"{artifact.File}\", \"sha256\": \"{Digest(artifact.Bytes)}\" }}"));
        var manifest = $$"""
            {
              "schema": "truth-release.v1",
              "source": {
                "source_repo": "the-omega-institute/trureturing",
                "source_commit": "{{manifestCommit}}",
                "source_tree": "{{manifestTree}}"
              },
              "trust": {
                "commit_on_protected_dev": true,
                "required_checks": [
                  { "name": "Candidate harness engineering checks", "conclusion": "success" },
                  { "name": "Canonical Lean report production", "conclusion": "success" },
                  { "name": "Content-addressed dev baseline admission", "conclusion": "success" }
                ]
              },
              "producer": {
                "package_repo": "the-omega-institute/trureturing-fkst-packages",
                "package_commit": "4444444444444444444444444444444444444444",
                "read_only": true
              },
              "artifacts": {
            {{artifactJson}}
              },
              "sha256sums_digest": "{{releaseDigest}}",
              "produced_at": "2026-08-22T00:00:00Z"
            }
            """;

        var directory = Directory.CreateTempSubdirectory("truthverify").FullName;
        foreach (var artifact in artifacts)
        {
            File.WriteAllBytes(Path.Combine(directory, artifact.File), artifact.Bytes);
        }

        File.WriteAllText(Path.Combine(directory, "SHA256SUMS"), sums, Utf8);
        File.WriteAllText(Path.Combine(directory, "release-manifest.v1.json"), manifest, Utf8);
        return (directory, releaseDigest);
    }

    [Fact]
    public void VerifiesACoherentBundle()
    {
        var (directory, digest) = BuildBundle();
        try
        {
            var verified = TruthReleaseVerification.Verify(directory, digest);

            Assert.Equal(digest, verified.ReleaseDigest);
            Assert.Equal("truth-export.v1.json", verified.Manifest.Artifacts.TruthExport.File);
            Assert.Equal(Commit, verified.Manifest.Source.SourceCommit);
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [Fact]
    public void RejectsSnapshotCommitFromAnotherRevision() =>
        AssertCompositionRejected(() => BuildBundle(snapshotCommit: OtherCommit));

    [Fact]
    public void RejectsTruthExportCommitFromAnotherRevision() =>
        AssertCompositionRejected(() => BuildBundle(exportCommit: OtherCommit));

    [Fact]
    public void RejectsManifestCommitFromAnotherRevision() =>
        AssertCompositionRejected(() => BuildBundle(manifestCommit: OtherCommit));

    [Fact]
    public void RejectsSnapshotTreeFromAnotherRevision() =>
        AssertCompositionRejected(() => BuildBundle(snapshotTree: OtherTree));

    [Fact]
    public void RejectsTruthExportTreeFromAnotherRevision() =>
        AssertCompositionRejected(() => BuildBundle(exportTree: OtherTree));

    [Fact]
    public void RejectsManifestTreeFromAnotherRevision() =>
        AssertCompositionRejected(() => BuildBundle(manifestTree: OtherTree));

    [Fact]
    public void RejectsSnapshotDigestNamingADifferentValidTruthGraph()
    {
        var otherGraph = MinimalTruthGraphBytes(
            "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd");
        Assert.Equal(TruthGraphExportModel.Dialect, TruthGraphJsonReader.Read(otherGraph).Schema);

        AssertCompositionRejected(() => BuildBundle(snapshotTruthGraphDigest: Digest(otherGraph)));
    }

    [Fact]
    public void RejectsACorrectlyHashedMalformedTruthGraph() =>
        AssertCompositionRejected(() => BuildBundle(truthGraph: Utf8.GetBytes("{}")));

    [Fact]
    public void RejectsACorrectlyHashedMalformedTruthExport() =>
        AssertCompositionRejected(() => BuildBundle(truthExport: Utf8.GetBytes("{}")));

    [Fact]
    public void RejectsAnExpectedDigestThatDoesNotMatchTheBundle()
    {
        var (directory, _) = BuildBundle();
        try
        {
            var wrong = "sha256:" + new string('0', 64);
            Assert.Throws<FormatException>(() => TruthReleaseVerification.Verify(directory, wrong));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [Fact]
    public void RejectsATamperedArtifact()
    {
        var (directory, digest) = BuildBundle();
        try
        {
            File.WriteAllText(Path.Combine(directory, "truth-export.v1.json"), "tampered", Utf8);
            Assert.Throws<FormatException>(() => TruthReleaseVerification.Verify(directory, digest));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [Fact]
    public void RejectsAMissingArtifactFile()
    {
        var (directory, digest) = BuildBundle();
        try
        {
            File.Delete(Path.Combine(directory, "truth-export.v1.json"));
            Assert.Throws<FormatException>(() => TruthReleaseVerification.Verify(directory, digest));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [Fact]
    public void RejectsATraversalFilenameInTheManifest()
    {
        var (directory, digest) = BuildBundle();
        try
        {
            var manifestPath = Path.Combine(directory, "release-manifest.v1.json");
            var evil = File.ReadAllText(manifestPath, Utf8)
                .Replace("\"truth-export.v1.json\"", "\"../escape.json\"", StringComparison.Ordinal);
            File.WriteAllText(manifestPath, evil, Utf8);
            Assert.Throws<FormatException>(() => TruthReleaseVerification.Verify(directory, digest));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [Fact]
    public void RejectsADuplicateArtifactFilename()
    {
        var (directory, digest) = BuildBundle();
        try
        {
            var manifestPath = Path.Combine(directory, "release-manifest.v1.json");
            var duplicate = File.ReadAllText(manifestPath, Utf8)
                .Replace("\"truth-graph.v1.json\"", "\"truth-export.v1.json\"", StringComparison.Ordinal);
            File.WriteAllText(manifestPath, duplicate, Utf8);
            Assert.Throws<FormatException>(() => TruthReleaseVerification.Verify(directory, digest));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [Fact]
    public void RejectsASymlinkedArtifact()
    {
        var (directory, digest) = BuildBundle();
        var externalDirectory = Directory.CreateTempSubdirectory("truthverify-ext").FullName;
        try
        {
            var external = Path.Combine(externalDirectory, "external.txt");
            File.WriteAllBytes(external, TruthExportBytes(Commit, Tree));
            var artifact = Path.Combine(directory, "truth-export.v1.json");
            File.Delete(artifact);
            File.CreateSymbolicLink(artifact, external);
            Assert.Throws<FormatException>(() => TruthReleaseVerification.Verify(directory, digest));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
            Directory.Delete(externalDirectory, recursive: true);
        }
    }

    private static void AssertCompositionRejected(Func<(string Directory, string Digest)> build)
    {
        var (directory, digest) = build();
        try
        {
            Assert.Throws<FormatException>(() => TruthReleaseVerification.Verify(directory, digest));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }
}
