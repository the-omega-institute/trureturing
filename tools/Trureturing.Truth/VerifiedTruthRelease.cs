namespace Trureturing.Truth;

/// <summary>
/// A truth-release bundle that has passed <see cref="TruthReleaseVerification.Verify"/> against an
/// out-of-band expected release digest: every artifact's bytes hash to the value SHA256SUMS records,
/// and the SHA256SUMS bytes hash to the expected digest. Holding an instance is evidence the bundle's
/// bytes are internally consistent with that digest.
/// <para>
/// This is a correctness boundary, NOT a security sandbox: the private constructor keeps ordinary code
/// from fabricating a "verified" value, but reflection or unsafe code in a full-trust process can still
/// bypass it. Authenticity comes from the out-of-band digest (and, for provenance, from independently
/// re-deriving the bundle and re-querying the commit's checks), never from this type's access modifiers.
/// </para>
/// </summary>
public sealed class VerifiedTruthRelease
{
    private VerifiedTruthRelease(TruthReleaseManifest manifest, string releaseDigest)
    {
        Manifest = manifest;
        ReleaseDigest = releaseDigest;
    }

    /// <summary>The parsed manifest of the verified bundle.</summary>
    public TruthReleaseManifest Manifest { get; }

    /// <summary>The out-of-band "sha256:&lt;64hex&gt;" digest this bundle was verified against.</summary>
    public string ReleaseDigest { get; }

    /// <summary>
    /// The sole mint path. It is <c>internal</c> so that only <see cref="TruthReleaseVerification"/> in
    /// this assembly can call it — external consumers cannot construct a verified value and MUST obtain
    /// one through <see cref="TruthReleaseVerification.Verify"/>. No <c>InternalsVisibleTo</c> is granted.
    /// </summary>
    internal static VerifiedTruthRelease Create(TruthReleaseManifest manifest, string releaseDigest) =>
        new(manifest, releaseDigest);
}
