namespace Trureturing.Truth;

/// <summary>
/// Resolves the publication-to-bundle integrity boundary. The caller supplies the physical bundle
/// directory selected by deployment; this verifier proves that those bytes have the publication's
/// release digest and that the verified bundle carries the same source and producer coordinates.
/// </summary>
public static class TruthReleasePublicationVerification
{
    public static VerifiedTruthRelease Verify(
        string bundleDirectory,
        TruthReleasePublication publication)
    {
        ArgumentNullException.ThrowIfNull(bundleDirectory);
        ArgumentNullException.ThrowIfNull(publication);

        // Reuse the canonical writer and strict reader so a programmatically constructed model cannot
        // bypass the exact schema or the bundle_ref == release_digest invariant.
        var publicationBytes = TruthReleasePublicationJsonWriter.Write(publication);
        var validated = TruthReleasePublicationReader.Read(publicationBytes.AsSpan());
        var verified = TruthReleaseVerification.Verify(
            bundleDirectory,
            validated.ReleaseDigest);

        if (!string.Equals(
                verified.Manifest.Source.SourceCommit,
                validated.SourceCommit,
                StringComparison.Ordinal))
        {
            throw new FormatException(
                "truth-release-publication source_commit does not name the verified bundle source.");
        }

        if (!string.Equals(
                verified.Manifest.Source.SourceTree,
                validated.SourceTree,
                StringComparison.Ordinal))
        {
            throw new FormatException(
                "truth-release-publication source_tree does not name the verified bundle source.");
        }

        if (!string.Equals(
                verified.Manifest.Producer.PackageCommit,
                validated.ProducerCommit,
                StringComparison.Ordinal))
        {
            throw new FormatException(
                "truth-release-publication producer_commit does not name the verified bundle producer.");
        }

        return verified;
    }
}
