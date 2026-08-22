namespace Trureturing.Truth;

/// <summary>
/// A truth-release bundle that has passed <see cref="TruthReleaseVerification.Verify"/> against an
/// out-of-band expected release digest: every artifact's bytes hash to the value SHA256SUMS records,
/// and the SHA256SUMS bytes hash to the expected digest. Holding an instance is evidence the bundle's
/// bytes are internally consistent with that digest.
/// <para>
/// Read bundle contents ONLY through the logical accessors (<see cref="ReadTruthGraph"/>,
/// <see cref="ReadTruthExport"/>). Each rereads its artifact by the manifest-recorded digest, rehashes the
/// bytes it read, and parses only those bytes, so a consumer never opens a manifest filename (the physical
/// bundle layout never leaks downstream, and a future index+shards format can land behind the same API)
/// and the verify/use TOCTOU is closed (bytes changed after <c>Verify</c> are rejected at read time).
/// </para>
/// <para>
/// This is a correctness boundary, NOT a security sandbox: the private constructor keeps ordinary code
/// from fabricating a "verified" value, but reflection or unsafe code in a full-trust process can still
/// bypass it. Authenticity comes from the out-of-band digest (and, for provenance, from independently
/// re-deriving the bundle and re-querying the commit's checks), never from this type's access modifiers.
/// </para>
/// </summary>
public sealed class VerifiedTruthRelease
{
    private readonly string _bundleDirectory;

    private VerifiedTruthRelease(TruthReleaseManifest manifest, string releaseDigest, string bundleDirectory)
    {
        Manifest = manifest;
        ReleaseDigest = releaseDigest;
        _bundleDirectory = bundleDirectory;
    }

    /// <summary>The parsed manifest of the verified bundle.</summary>
    public TruthReleaseManifest Manifest { get; }

    /// <summary>The out-of-band "sha256:&lt;64hex&gt;" digest this bundle was verified against.</summary>
    public string ReleaseDigest { get; }

    /// <summary>
    /// Reads the <c>truth_graph</c> artifact through its verified digest and returns the typed model. The
    /// bytes are reread and rehashed against the digest verification bound, so bytes changed after
    /// <see cref="TruthReleaseVerification.Verify"/> are rejected. Use this instead of opening
    /// <c>Manifest.Artifacts.TruthGraph.File</c> directly.
    /// </summary>
    public TruthGraphExportModel ReadTruthGraph() =>
        TruthGraphJsonReader.Read(
            TruthReleaseVerification.ReadVerifiedArtifactBytes(_bundleDirectory, Manifest.Artifacts.TruthGraph));

    /// <summary>
    /// Reads the strict active-frozen <c>truth_export</c> artifact through its verified digest and returns
    /// the typed model, with the same reread-and-rehash TOCTOU guarantee as <see cref="ReadTruthGraph"/>.
    /// </summary>
    public TruthExportModel ReadTruthExport() =>
        TruthExportJsonReader.Read(
            TruthReleaseVerification.ReadVerifiedArtifactBytes(_bundleDirectory, Manifest.Artifacts.TruthExport));

    /// <summary>
    /// The sole mint path. It is <c>internal</c> so that only <see cref="TruthReleaseVerification"/> in
    /// this assembly can call it — external consumers cannot construct a verified value and MUST obtain
    /// one through <see cref="TruthReleaseVerification.Verify"/>. No <c>InternalsVisibleTo</c> is granted.
    /// </summary>
    internal static VerifiedTruthRelease Create(
        TruthReleaseManifest manifest, string releaseDigest, string bundleDirectory) =>
        new(manifest, releaseDigest, bundleDirectory);
}
