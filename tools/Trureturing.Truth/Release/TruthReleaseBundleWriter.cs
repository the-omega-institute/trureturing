using System.Collections.Immutable;
using System.Text;

namespace Trureturing.Truth;

/// <summary>The typed inputs needed to assemble the seven-artifact truth-release bundle.</summary>
public sealed record TruthReleaseBundleInput(
    SourceSnapshotModel SourceSnapshot,
    ImmutableArray<byte> TruthGraphBytes,
    ImmutableArray<byte> RawLeanReportBytes,
    ImmutableArray<byte> TruthExportBytes,
    ImmutableArray<byte> BlueprintIndexBytes,
    ImmutableArray<byte> FrozenLedgerHeadBytes,
    ImmutableArray<byte> ResidualFrontierBytes,
    TruthReleaseSource Source,
    TruthReleaseTrust Trust,
    TruthReleaseProducer Producer,
    string ProducedAt);

/// <summary>
/// The package-owned write authority for a truth-release bundle. It assigns every wire filename,
/// hashes the exact artifact bytes it writes, emits canonical SHA256SUMS, emits the canonical manifest,
/// and finally publishes a transport-neutral coordinate for downstream services.
/// </summary>
public static class TruthReleaseBundleWriter
{
    public const string SourceSnapshotFileName = "source-snapshot.v1.json";
    public const string TruthGraphFileName = "truth-graph.v1.json";
    public const string RawLeanReportFileName = "raw-lean-report.json";
    public const string TruthExportFileName = "truth-export.v1.json";
    public const string BlueprintIndexFileName = "blueprint-index.v1.json";
    public const string FrozenLedgerHeadFileName = "frozen-ledger-head.json";
    public const string ResidualFrontierFileName = "echo-residual-summary.md";
    public const string Sha256SumsFileName = "SHA256SUMS";
    public const string ManifestFileName = "release-manifest.v1.json";
    public const string PublicationFileName = "truth-release-publication.v1.json";

    private static readonly UTF8Encoding Utf8 = new(false, true);

    public static string WriteBundle(string outputDirectory, TruthReleaseBundleInput input)
    {
        ArgumentNullException.ThrowIfNull(outputDirectory);
        ArgumentNullException.ThrowIfNull(input);
        ArgumentNullException.ThrowIfNull(input.SourceSnapshot);
        ArgumentNullException.ThrowIfNull(input.Source);
        ArgumentNullException.ThrowIfNull(input.Trust);
        ArgumentNullException.ThrowIfNull(input.Producer);
        ArgumentNullException.ThrowIfNull(input.ProducedAt);

        Directory.CreateDirectory(outputDirectory);
        var artifacts = new[]
        {
            new ArtifactBytes(SourceSnapshotFileName, SourceSnapshotJsonWriter.Write(input.SourceSnapshot)),
            new ArtifactBytes(TruthGraphFileName, input.TruthGraphBytes),
            new ArtifactBytes(RawLeanReportFileName, input.RawLeanReportBytes),
            new ArtifactBytes(TruthExportFileName, input.TruthExportBytes),
            new ArtifactBytes(BlueprintIndexFileName, input.BlueprintIndexBytes),
            new ArtifactBytes(FrozenLedgerHeadFileName, input.FrozenLedgerHeadBytes),
            new ArtifactBytes(ResidualFrontierFileName, input.ResidualFrontierBytes),
        };

        foreach (var artifact in artifacts)
        {
            File.WriteAllBytes(Path.Combine(outputDirectory, artifact.File), artifact.Bytes.ToArray());
        }

        var hexByName = artifacts.ToDictionary(
            static artifact => artifact.File,
            static artifact => Sha256Sums.HashHex(artifact.Bytes.AsSpan()),
            StringComparer.Ordinal);
        var sumsBytes = Utf8.GetBytes(Sha256Sums.Format(hexByName));
        File.WriteAllBytes(Path.Combine(outputDirectory, Sha256SumsFileName), sumsBytes);
        var releaseDigest = Sha256Sums.ReleaseDigest(sumsBytes);

        TruthReleaseArtifact Artifact(string file) => new(file, "sha256:" + hexByName[file]);
        var manifest = new TruthReleaseManifest(
            input.Source,
            input.Trust,
            input.Producer,
            new TruthReleaseArtifacts(
                Artifact(SourceSnapshotFileName),
                Artifact(TruthGraphFileName),
                Artifact(RawLeanReportFileName),
                Artifact(TruthExportFileName),
                Artifact(BlueprintIndexFileName),
                Artifact(FrozenLedgerHeadFileName),
                Artifact(ResidualFrontierFileName)),
            releaseDigest,
            input.ProducedAt);
        var manifestBytes = TruthReleaseManifestJsonWriter.Write(manifest);
        File.WriteAllBytes(Path.Combine(outputDirectory, ManifestFileName), manifestBytes.ToArray());

        // This coordinate is intentionally outside SHA256SUMS. It names the already-complete bundle
        // by the out-of-band release digest and carries no physical locator, queue, or consumer semantics.
        var publication = new TruthReleasePublication(
            releaseDigest,
            releaseDigest,
            input.Source.SourceCommit,
            input.Source.SourceTree,
            input.Producer.PackageCommit);
        var publicationBytes = TruthReleasePublicationJsonWriter.Write(publication);
        File.WriteAllBytes(
            Path.Combine(outputDirectory, PublicationFileName),
            publicationBytes.ToArray());
        return releaseDigest;
    }

    private sealed record ArtifactBytes(string File, ImmutableArray<byte> Bytes);
}
