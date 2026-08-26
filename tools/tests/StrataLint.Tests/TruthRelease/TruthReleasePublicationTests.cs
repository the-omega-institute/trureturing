using System.Collections.Immutable;
using System.Text;
using Trureturing.Truth;
using Xunit;

namespace StrataLint.Tests;

public sealed class TruthReleasePublicationTests
{
    private const string SourceCommit = "1111111111111111111111111111111111111111";
    private const string SourceTree = "2222222222222222222222222222222222222222";
    private const string ProducerCommit = "3333333333333333333333333333333333333333";
    private const string ReleaseDigest =
        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";

    [Fact]
    public void WriterEmitsCanonicalFixedOrderUtf8WithFinalLf()
    {
        var publication = Publication();

        var bytes = TruthReleasePublicationJsonWriter.Write(publication);

        Assert.Equal(
            "{\"bundle_ref\": \"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\", "
                + "\"producer_commit\": \"3333333333333333333333333333333333333333\", "
                + "\"release_digest\": \"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\", "
                + "\"schema\": \"truth-release-publication.v1\", "
                + "\"source_commit\": \"1111111111111111111111111111111111111111\", "
                + "\"source_tree\": \"2222222222222222222222222222222222222222\"}\n",
            Encoding.UTF8.GetString(bytes.AsSpan()));
        Assert.Equal((byte)'\n', bytes[^1]);
        Assert.Equal(publication, TruthReleasePublicationReader.Read(bytes.AsSpan()));
    }

    [Fact]
    public void ReaderRejectsDuplicateProperties()
    {
        var json = "{\"schema\":\"truth-release-publication.v1\","
            + "\"schema\":\"truth-release-publication.v1\","
            + FieldsAfterSchema();

        Assert.Throws<FormatException>(() => TruthReleasePublicationReader.Read(json));
    }

    [Fact]
    public void ReaderRejectsUnknownProperties()
    {
        var json = ValidJson()[..^1] + ",\"transport\":\"github\"}";

        Assert.Throws<FormatException>(() => TruthReleasePublicationReader.Read(json));
    }

    [Fact]
    public void ReaderRejectsMissingProperties()
    {
        var json = "{\"schema\":\"truth-release-publication.v1\","
            + "\"release_digest\":\"" + ReleaseDigest + "\","
            + "\"bundle_ref\":\"" + ReleaseDigest + "\","
            + "\"source_commit\":\"" + SourceCommit + "\","
            + "\"producer_commit\":\"" + ProducerCommit + "\"}";

        Assert.Throws<FormatException>(() => TruthReleasePublicationReader.Read(json));
    }

    [Fact]
    public void ReaderRejectsWrongFieldTypes()
    {
        var json = ValidJson().Replace(
            "\"release_digest\":\"" + ReleaseDigest + "\"",
            "\"release_digest\":7",
            StringComparison.Ordinal);

        Assert.Throws<FormatException>(() => TruthReleasePublicationReader.Read(json));
    }

    [Fact]
    public void ReaderRejectsBundleRebinding()
    {
        var json = ValidJson().Replace(
            "\"bundle_ref\":\"" + ReleaseDigest + "\"",
            "\"bundle_ref\":\"sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\"",
            StringComparison.Ordinal);

        var error = Assert.Throws<FormatException>(
            () => TruthReleasePublicationReader.Read(json));

        Assert.Contains("bundle_ref must equal release_digest", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ReaderRejectsMalformedSha256AndGitObjects()
    {
        var malformedDigest = ValidJson().Replace(
            ReleaseDigest,
            "sha256:AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA",
            StringComparison.Ordinal);
        var malformedCommit = ValidJson().Replace(
            SourceCommit,
            "1111",
            StringComparison.Ordinal);

        Assert.Throws<FormatException>(() => TruthReleasePublicationReader.Read(malformedDigest));
        Assert.Throws<FormatException>(() => TruthReleasePublicationReader.Read(malformedCommit));
    }

    [Fact]
    public void ReaderRejectsMixedSourceGitObjectFormats()
    {
        var json = ValidJson().Replace(
            SourceTree,
            new string('2', 64),
            StringComparison.Ordinal);

        Assert.Throws<FormatException>(() => TruthReleasePublicationReader.Read(json));
    }

    [Fact]
    public void BundleWriterEmitsCoordinateForTheExactVerifiedBundle()
    {
        var directory = Directory.CreateTempSubdirectory("truth-release-publication").FullName;
        try
        {
            var input = BundleInput();

            var releaseDigest = TruthReleaseBundleWriter.WriteBundle(directory, input);
            var publicationBytes = File.ReadAllBytes(Path.Combine(
                directory,
                TruthReleaseBundleWriter.PublicationFileName));
            var publication = TruthReleasePublicationReader.Read(publicationBytes);
            var verified = TruthReleasePublicationVerification.Verify(directory, publication);

            Assert.Equal(releaseDigest, verified.ReleaseDigest);
            Assert.Equal(releaseDigest, publication.ReleaseDigest);
            Assert.Equal(releaseDigest, publication.BundleRef);
            Assert.Equal(input.Source.SourceCommit, publication.SourceCommit);
            Assert.Equal(input.Source.SourceTree, publication.SourceTree);
            Assert.Equal(input.Producer.PackageCommit, publication.ProducerCommit);
            Assert.Equal(
                publicationBytes,
                TruthReleasePublicationJsonWriter.Write(publication).ToArray());
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [Fact]
    public void PublicationVerificationRejectsSourceAndProducerRebinding()
    {
        var directory = Directory.CreateTempSubdirectory("truth-release-publication-rebinding").FullName;
        try
        {
            var input = BundleInput();
            _ = TruthReleaseBundleWriter.WriteBundle(directory, input);
            var publication = TruthReleasePublicationReader.Read(File.ReadAllBytes(Path.Combine(
                directory,
                TruthReleaseBundleWriter.PublicationFileName)));

            Assert.Throws<FormatException>(() => TruthReleasePublicationVerification.Verify(
                directory,
                publication with { SourceCommit = new string('9', 40) }));
            Assert.Throws<FormatException>(() => TruthReleasePublicationVerification.Verify(
                directory,
                publication with { SourceTree = new string('8', 40) }));
            Assert.Throws<FormatException>(() => TruthReleasePublicationVerification.Verify(
                directory,
                publication with { ProducerCommit = new string('7', 40) }));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    private static TruthReleasePublication Publication() =>
        new(ReleaseDigest, ReleaseDigest, SourceCommit, SourceTree, ProducerCommit);

    private static string ValidJson() =>
        "{\"schema\":\"truth-release-publication.v1\"," + FieldsAfterSchema();

    private static string FieldsAfterSchema() =>
        "\"release_digest\":\"" + ReleaseDigest + "\","
        + "\"bundle_ref\":\"" + ReleaseDigest + "\","
        + "\"source_commit\":\"" + SourceCommit + "\","
        + "\"source_tree\":\"" + SourceTree + "\","
        + "\"producer_commit\":\"" + ProducerCommit + "\"}";

    private static TruthReleaseBundleInput BundleInput()
    {
        var truthGraph = TruthGraphJsonWriter.Write(MinimalTruthGraph());
        var rawLeanReport = Bytes(
            "{\"modules\": [], \"schema\": \"stratalint-raw-lean-report-v1\"}\n");
        var truthExport = TruthExportJsonWriter.Write(MinimalTruthExport());
        var blueprintIndex = Bytes("{\"entries\":[]}\n");
        var frozenLedgerHead = Bytes("{\"sequence\":0}\n");
        var residualFrontier = Bytes("# Residual frontier\n");
        var sourceSnapshot = new SourceSnapshotModel(
            "source-snapshot.v1",
            "the-omega-institute/trureturing",
            SourceCommit,
            SourceTree,
            "leanprover/lean4:v4.24.0",
            "4444444444444444444444444444444444444444",
            ProducerCommit,
            Digest(truthGraph),
            Digest(rawLeanReport),
            Digest(blueprintIndex),
            Digest(residualFrontier),
            Digest(truthExport),
            Digest(frozenLedgerHead),
            0);
        return new TruthReleaseBundleInput(
            sourceSnapshot,
            truthGraph,
            rawLeanReport,
            truthExport,
            blueprintIndex,
            frozenLedgerHead,
            residualFrontier,
            new TruthReleaseSource(
                "the-omega-institute/trureturing",
                SourceCommit,
                SourceTree),
            new TruthReleaseTrust(
                CommitOnProtectedDev: true,
                ImmutableArray.Create(
                    new TruthReleaseRequiredCheck(
                        "Candidate harness engineering checks",
                        "success"),
                    new TruthReleaseRequiredCheck(
                        "Canonical Lean report production",
                        "success"),
                    new TruthReleaseRequiredCheck(
                        "Content-addressed dev baseline admission",
                        "success")),
                BlessedBy: null),
            new TruthReleaseProducer(
                "the-omega-institute/trureturing",
                ProducerCommit,
                ReadOnly: true),
            "2026-08-26T00:00:00Z");
    }

    private static TruthGraphExportModel MinimalTruthGraph() =>
        new(
            TruthGraphExportModel.Dialect,
            1,
            new TruthGraphProvenance(
                "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
                "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc")
            {
                TruthRootSha256 =
                    "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd",
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
                "sha256:eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee",
                ImmutableArray.Create("propext"),
                ImmutableArray.Create(new TruthExportDeclaration(
                    "nk-a",
                    "theorem",
                    "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")),
                ImmutableArray<string>.Empty)),
            SourceCommit,
            SourceTree);

    private static ImmutableArray<byte> Bytes(string text) =>
        ImmutableArray.CreateRange(new UTF8Encoding(false).GetBytes(text));

    private static string Digest(ImmutableArray<byte> bytes) =>
        "sha256:" + Sha256Sums.HashHex(bytes.AsSpan());
}
