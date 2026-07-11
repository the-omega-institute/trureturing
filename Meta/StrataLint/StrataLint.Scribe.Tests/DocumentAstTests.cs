using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class DocumentAstTests
{
    [Fact]
    public void GidRefRejectsInvalidSyntaxAtConstruction()
    {
        Assert.Throws<ArgumentException>(() => GidRef.Create("D5/S1/Scale/Embedding@bad"));
    }

    [Fact]
    public void SnapshotValidatorRejectsReferencesToMissingArtifacts()
    {
        var raw = RawRepositorySnapshot.Create(
        [
            RawRepositoryEntry.FromText("D5/S1/Scale/Embedding.lean", "namespace Test\n"),
        ]);
        var decoded = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw));
        var validator = new SnapshotGidExistenceValidator(decoded.Snapshot);

        var existing = GidRef.Create(
            "D5/S1/Scale/Embedding.embedding_injective",
            validator);

        Assert.Equal("D5/S1/Scale/Embedding.embedding_injective", existing.Value);
        Assert.Throws<ArgumentException>(() =>
            GidRef.Create("D5/S1/Scale/Log.logScale_zero", validator));
    }

    [Fact]
    public void DocumentHeaderCarriesTypedMirrorAndProvenanceFields()
    {
        var header = DocumentHeader.Create(
            GidRef.Create("D5/S1/Scale/Embedding"),
            Generality.Instance,
            GidRef.Create("D5/B/S1/Scale/Embedding"),
            new EvidenceMirror.Waiver(WaiverReason.Create("algebraically-proved")),
            [AnchorRef.Create("GICT-v3.6-I.1-definition-1.4")],
            Digest.Create("The real embedding is injective."));

        Assert.Equal(Generality.Instance, header.Generality);
        Assert.Equal("D5/B/S1/Scale/Embedding", header.MirrorBlueprint.Value);
        Assert.Equal(
            "GICT-v3.6-I.1-definition-1.4",
            Assert.Single(header.Anchors).Value);
        Assert.Equal("The real embedding is injective.", header.Digest.Value);
    }

    [Fact]
    public void DocumentHeaderRejectsMismatchedBlueprintMirror()
    {
        Assert.Throws<ArgumentException>(() => DocumentHeader.Create(
            GidRef.Create("D5/S1/Scale/Embedding"),
            Generality.Instance,
            GidRef.Create("D5/B/S1/Scale/Log"),
            new EvidenceMirror.Waiver(WaiverReason.Create("algebraically-proved")),
            ImmutableArray<AnchorRef>.Empty,
            Digest.Create("Embedding.")));
    }

    [Theory]
    [InlineData("D5/B/S1/Scale/Embedding")]
    [InlineData("D5/S1/Scale/Embedding")]
    public void LeanDeclarationRefRejectsNonDeclarationGids(string value)
    {
        Assert.Throws<ArgumentException>(() => LeanDeclarationRef.Create(value));
    }
}
