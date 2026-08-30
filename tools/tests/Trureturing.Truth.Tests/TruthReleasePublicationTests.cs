using System.Text;
using Trureturing.Truth;
using Xunit;

namespace Trureturing.Truth.Tests;

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

}
