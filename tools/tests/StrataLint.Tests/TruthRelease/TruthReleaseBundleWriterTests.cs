using System;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using System.Text;
using Trureturing.Truth;
using Xunit;
using Xunit.Sdk;

namespace StrataLint.Tests;

public sealed class TruthReleaseBundleWriterTests
{
    private const string SourceCommit = "1111111111111111111111111111111111111111";
    private const string SourceTree = "2222222222222222222222222222222222222222";
    private const string PackageCommit = "3333333333333333333333333333333333333333";

    [Fact]
    public void SourceSnapshotWriterRoundTripsAllFourteenFields()
    {
        var expected = CreateSourceSnapshot(
            Digest(Utf8("truth graph\n")),
            Utf8("raw report\n"),
            Utf8("blueprint index\n"),
            Utf8("frozen ledger head\n"),
            Utf8("residual frontier\n"),
            Utf8("truth export\n"));

        var bytes = SourceSnapshotJsonWriter.Write(expected);
        var actual = SourceSnapshotJsonReader.Read(bytes.AsSpan());

        Assert.Equal(expected, actual);
        Assert.Equal(bytes.ToArray(), SourceSnapshotJsonWriter.Write(actual).ToArray());
    }

    [Fact]
    public void ManifestWriterRoundTripsEverySchemaField()
    {
        var expected = new TruthReleaseManifest(
            Source(),
            Trust(blessedBy: "release-test"),
            Producer(),
            new TruthReleaseArtifacts(
                Artifact("source-snapshot.v1.json", '1'),
                Artifact("truth-graph.v1.json", '2'),
                Artifact("raw-lean-report.json", '3'),
                Artifact("truth-export.v1.json", '4'),
                Artifact("blueprint-index.v1.json", '5'),
                Artifact("frozen-ledger-head.json", '6'),
                Artifact("echo-residual-summary.md", '7')),
            "sha256:" + new string('8', 64),
            "2026-08-23T00:00:00Z");

        var bytes = TruthReleaseManifestJsonWriter.Write(expected);
        var actual = TruthReleaseManifestReader.Read(Encoding.UTF8.GetString(bytes.AsSpan()));

        Assert.Equal(expected.Source, actual.Source);
        Assert.Equal(expected.Trust.CommitOnProtectedDev, actual.Trust.CommitOnProtectedDev);
        Assert.Equal(expected.Trust.RequiredChecks.ToArray(), actual.Trust.RequiredChecks.ToArray());
        Assert.Equal(expected.Trust.BlessedBy, actual.Trust.BlessedBy);
        Assert.Equal(expected.Producer, actual.Producer);
        Assert.Equal(expected.Artifacts, actual.Artifacts);
        Assert.Equal(expected.Sha256SumsDigest, actual.Sha256SumsDigest);
        Assert.Equal(expected.ProducedAt, actual.ProducedAt);
        Assert.Equal(bytes.ToArray(), TruthReleaseManifestJsonWriter.Write(actual).ToArray());
    }

    [Fact]
    public void WriterProducesAVerifiableSchemaSymmetricBundle()
    {
        var fixture = CreateBundleFixture();
        var directory = Directory.CreateTempSubdirectory("truthbundle-writer").FullName;
        try
        {
            var releaseDigest = TruthReleaseBundleWriter.WriteBundle(directory, fixture.Input);

            var verified = TruthReleaseVerification.Verify(directory, releaseDigest);
            var publicationPath = Path.Combine(
                directory,
                TruthReleaseBundleWriter.PublicationFileName);
            var publicationBytes = TemporaryFileSystem.File.ReadAllBytes(publicationPath);
            var publication = TruthReleasePublicationReader.Read(publicationBytes);
            var publicationVerified = TruthReleasePublicationVerification.Verify(directory, publication);
            var canonicalPublicationBytes = TruthReleasePublicationJsonWriter.Write(publication).ToArray();

            Assert.Equal(releaseDigest, verified.ReleaseDigest);
            Assert.Equal(releaseDigest, publicationVerified.ReleaseDigest);
            Assert.Equal(releaseDigest, publication.ReleaseDigest);
            Assert.Equal(releaseDigest, publication.BundleRef);
            Assert.Equal(fixture.Input.Source.SourceCommit, publication.SourceCommit);
            Assert.Equal(fixture.Input.Source.SourceTree, publication.SourceTree);
            Assert.Equal(fixture.Input.Producer.PackageCommit, publication.ProducerCommit);
            AssertPublicationBytesAreCanonical(publicationPath, canonicalPublicationBytes);
            Assert.Equal((byte)'\n', canonicalPublicationBytes[^1]);
            var hostilePublicationBytes = new (string Name, byte[] Bytes)[]
            {
                ("UTF-8 BOM", [.. Encoding.UTF8.Preamble, .. canonicalPublicationBytes]),
                ("CRLF", Encoding.UTF8.GetBytes(
                    Encoding.UTF8.GetString(canonicalPublicationBytes)
                        .Replace("\n", "\r\n", StringComparison.Ordinal))),
                ("missing final LF", canonicalPublicationBytes[..^1]),
            };
            try
            {
                foreach (var hostile in hostilePublicationBytes)
                {
                    TemporaryFileSystem.File.WriteAllBytes(publicationPath, hostile.Bytes);
                    var failure = Record.Exception(
                        () => AssertPublicationBytesAreCanonical(publicationPath, canonicalPublicationBytes));
                    Assert.True(
                        failure is EqualException,
                        $"{hostile.Name} bytes must fail canonical raw-byte equality; observed "
                            + (failure?.GetType().FullName ?? "no failure"));
                }
            }
            finally
            {
                TemporaryFileSystem.File.WriteAllBytes(publicationPath, canonicalPublicationBytes);
            }
            Assert.Throws<FormatException>(() => TruthReleasePublicationVerification.Verify(
                directory,
                publication with { SourceCommit = new string('9', 40) }));
            Assert.Throws<FormatException>(() => TruthReleasePublicationVerification.Verify(
                directory,
                publication with { SourceTree = new string('8', 40) }));
            Assert.Throws<FormatException>(() => TruthReleasePublicationVerification.Verify(
                directory,
                publication with { ProducerCommit = new string('7', 40) }));
            Assert.Equal("source-snapshot.v1.json", verified.Manifest.Artifacts.SourceSnapshot.File);
            Assert.Equal("truth-graph.v1.json", verified.Manifest.Artifacts.TruthGraph.File);
            Assert.Equal("raw-lean-report.json", verified.Manifest.Artifacts.RawLeanReport.File);
            Assert.Equal("truth-export.v1.json", verified.Manifest.Artifacts.TruthExport.File);
            Assert.Equal("blueprint-index.v1.json", verified.Manifest.Artifacts.BlueprintIndex.File);
            Assert.Equal("frozen-ledger-head.json", verified.Manifest.Artifacts.FrozenLedgerHead.File);
            Assert.Equal("echo-residual-summary.md", verified.Manifest.Artifacts.ResidualFrontier.File);
            Assert.Equal(
                TruthGraphJsonWriter.Write(fixture.TruthGraph).ToArray(),
                TruthGraphJsonWriter.Write(verified.ReadTruthGraph()).ToArray());
            Assert.Equal(
                TruthExportJsonWriter.Write(fixture.TruthExport).ToArray(),
                TruthExportJsonWriter.Write(verified.ReadTruthExport()).ToArray());

            var sumNames = File.ReadAllLines(Path.Combine(directory, "SHA256SUMS"))
                .Select(static line => line[66..])
                .ToArray();
            Assert.Equal(sumNames.OrderBy(static name => name, StringComparer.Ordinal).ToArray(), sumNames);
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [Fact]
    public void VerifierRejectsSourceSnapshotRawLeanReportDigestThatDoesNotNameVerifiedArtifact()
    {
        var fixture = CreateBundleFixture();
        var input = fixture.Input with
        {
            SourceSnapshot = fixture.Input.SourceSnapshot with
            {
                RawLeanReportSha256 = "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            },
        };
        var directory = Directory.CreateTempSubdirectory("truthbundle-raw-report-composition").FullName;
        try
        {
            var releaseDigest = TruthReleaseBundleWriter.WriteBundle(directory, input);

            Assert.Throws<FormatException>(() => TruthReleaseVerification.Verify(directory, releaseDigest));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [Fact]
    public void VerifierRejectsSourceSnapshotResidualFrontierDigestThatDoesNotNameVerifiedArtifact()
    {
        var fixture = CreateBundleFixture();
        var input = fixture.Input with
        {
            SourceSnapshot = fixture.Input.SourceSnapshot with
            {
                ResidualFrontierSha256 = "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            },
        };
        var directory = Directory.CreateTempSubdirectory("truthbundle-residual-composition").FullName;
        try
        {
            var releaseDigest = TruthReleaseBundleWriter.WriteBundle(directory, input);

            Assert.Throws<FormatException>(() => TruthReleaseVerification.Verify(directory, releaseDigest));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [Fact]
    public void VerifierRejectsSourceSnapshotDeclarationsDigestThatDoesNotNameVerifiedArtifact()
    {
        var fixture = CreateBundleFixture();
        var input = fixture.Input with
        {
            SourceSnapshot = fixture.Input.SourceSnapshot with
            {
                DeclarationsSha256 = "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            },
        };
        var directory = Directory.CreateTempSubdirectory("truthbundle-declarations-composition").FullName;
        try
        {
            var releaseDigest = TruthReleaseBundleWriter.WriteBundle(directory, input);

            Assert.Throws<FormatException>(() => TruthReleaseVerification.Verify(directory, releaseDigest));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [Fact]
    public void VerifierRejectsSourceSnapshotFrozenLedgerHeadHashThatDoesNotNameVerifiedArtifact()
    {
        var fixture = CreateBundleFixture();
        var input = fixture.Input with
        {
            SourceSnapshot = fixture.Input.SourceSnapshot with
            {
                FrozenLedgerHeadHash = "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            },
        };
        var directory = Directory.CreateTempSubdirectory("truthbundle-frozen-ledger-head-composition").FullName;
        try
        {
            var releaseDigest = TruthReleaseBundleWriter.WriteBundle(directory, input);

            Assert.Throws<FormatException>(() => TruthReleaseVerification.Verify(directory, releaseDigest));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [Fact]
    public void VerifierAcceptsFullyCoherentBundle()
    {
        var fixture = CreateBundleFixture();
        var directory = Directory.CreateTempSubdirectory("truthbundle-coherent-composition").FullName;
        try
        {
            var releaseDigest = TruthReleaseBundleWriter.WriteBundle(directory, fixture.Input);

            var verified = TruthReleaseVerification.Verify(directory, releaseDigest);

            Assert.Equal(releaseDigest, verified.ReleaseDigest);
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [Fact]
    public void VerifierRejectsAnArtifactCorruptedAfterWriting()
    {
        var fixture = CreateBundleFixture();
        var directory = Directory.CreateTempSubdirectory("truthbundle-corrupt").FullName;
        try
        {
            var releaseDigest = TruthReleaseBundleWriter.WriteBundle(directory, fixture.Input);
            File.AppendAllText(
                Path.Combine(directory, "blueprint-index.v1.json"),
                "corrupt",
                new UTF8Encoding(false));

            Assert.Throws<FormatException>(() => TruthReleaseVerification.Verify(directory, releaseDigest));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    private static BundleFixture CreateBundleFixture()
    {
        var truthGraph = MinimalTruthGraph();
        var truthGraphBytes = TruthGraphJsonWriter.Write(truthGraph);
        var rawLeanReport = ImmutableArray.CreateRange(Utf8(
            "{\"modules\": [], \"schema\": \"stratalint-raw-lean-report-v2\"}\n"));
        var truthExport = MinimalTruthExport();
        var truthExportBytes = TruthExportJsonWriter.Write(truthExport);
        var blueprintIndex = ImmutableArray.CreateRange(Utf8("{\"blueprints\": []}\n"));
        var frozenLedgerHead = ImmutableArray.CreateRange(Utf8("{\"sequence\": 7}\n"));
        var residualFrontier = ImmutableArray.CreateRange(Utf8("# Residual frontier\n\nNone.\n"));
        var sourceSnapshot = CreateSourceSnapshot(
            "sha256:" + Sha256Sums.HashHex(truthGraphBytes.AsSpan()),
            rawLeanReport.ToArray(),
            blueprintIndex.ToArray(),
            frozenLedgerHead.ToArray(),
            residualFrontier.ToArray(),
            truthExportBytes.ToArray());
        var input = new TruthReleaseBundleInput(
            sourceSnapshot,
            truthGraphBytes,
            rawLeanReport,
            truthExportBytes,
            blueprintIndex,
            frozenLedgerHead,
            residualFrontier,
            Source(),
            Trust(blessedBy: null),
            Producer(),
            "2026-08-23T00:00:00Z");
        return new BundleFixture(input, truthGraph, truthExport);
    }

    private static SourceSnapshotModel CreateSourceSnapshot(
        string truthGraphDigest,
        byte[] rawLeanReport,
        byte[] blueprintIndex,
        byte[] frozenLedgerHead,
        byte[] residualFrontier,
        byte[] truthExport) =>
        new(
            "source-snapshot.v1",
            "the-omega-institute/trureturing",
            SourceCommit,
            SourceTree,
            "leanprover/lean4:v4.24.0",
            "4444444444444444444444444444444444444444",
            PackageCommit,
            truthGraphDigest,
            Digest(rawLeanReport),
            Digest(blueprintIndex),
            Digest(residualFrontier),
            Digest(truthExport),
            Digest(frozenLedgerHead),
            7);

    private static TruthGraphExportModel MinimalTruthGraph() =>
        new(
            TruthGraphExportModel.Dialect,
            1,
            new TruthGraphProvenance(
                "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb")
            {
                TruthRootSha256 = "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
                DependencyGranularity = "module-import",
            },
            new TruthGraphSection([], [], [], new TruthGraphStateCounts(0, 0, 0, 0)),
            new DocumentGraphSection([], [], [], []),
            new TruthGraphJoinsSection([]),
            ["digestion"]);

    private static TruthExportModel MinimalTruthExport() =>
        TruthExportModel.Create(
            ImmutableArray.Create(new TruthExportNode(
                "D5/S0/A.lean",
                "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                ImmutableArray.Create("propext"),
                ImmutableArray.Create(new TruthExportDeclaration(
                    "nk-a",
                    "theorem",
                    "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd")),
                ImmutableArray<string>.Empty)),
            SourceCommit,
            SourceTree);

    private static TruthReleaseSource Source() =>
        new("the-omega-institute/trureturing", SourceCommit, SourceTree);

    private static TruthReleaseTrust Trust(string? blessedBy) =>
        new(
            CommitOnProtectedDev: true,
            ImmutableArray.Create(
                new TruthReleaseRequiredCheck("Candidate harness engineering checks", "success"),
                new TruthReleaseRequiredCheck("Canonical Lean report production", "success"),
                new TruthReleaseRequiredCheck("Content-addressed dev baseline admission", "success")),
            blessedBy);

    private static TruthReleaseProducer Producer() =>
        new("the-omega-institute/trureturing-fkst-packages", PackageCommit, ReadOnly: true);

    private static TruthReleaseArtifact Artifact(string file, char digest) =>
        new(file, "sha256:" + new string(digest, 64));

    private static byte[] Utf8(string text) => new UTF8Encoding(false).GetBytes(text);

    private static string Digest(byte[] bytes) => "sha256:" + Sha256Sums.HashHex(bytes);

    private static void AssertPublicationBytesAreCanonical(string path, byte[] canonicalBytes) =>
        Assert.Equal(canonicalBytes, TemporaryFileSystem.File.ReadAllBytes(path));

    private static class TemporaryFileSystem
    {
        internal static class File
        {
            internal static byte[] ReadAllBytes(string path) => System.IO.File.ReadAllBytes(path);

            internal static void WriteAllBytes(string path, byte[] contents) =>
                System.IO.File.WriteAllBytes(path, contents);
        }
    }

    private sealed record BundleFixture(
        TruthReleaseBundleInput Input,
        TruthGraphExportModel TruthGraph,
        TruthExportModel TruthExport);
}
