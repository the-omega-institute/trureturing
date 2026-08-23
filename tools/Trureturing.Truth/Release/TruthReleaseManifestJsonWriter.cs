using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;

namespace Trureturing.Truth;

/// <summary>
/// Canonical writer for <c>release-manifest.v1.json</c>. It emits only the fields owned by the strict
/// reader and reads its output back before returning, making the package's manifest contract symmetric.
/// </summary>
public static class TruthReleaseManifestJsonWriter
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    private static readonly JsonSerializerOptions SerializerOptions = new()
    {
        DefaultIgnoreCondition = JsonIgnoreCondition.WhenWritingNull,
    };

    public static ImmutableArray<byte> Write(TruthReleaseManifest manifest)
    {
        ArgumentNullException.ThrowIfNull(manifest);
        ArgumentNullException.ThrowIfNull(manifest.Source);
        ArgumentNullException.ThrowIfNull(manifest.Trust);
        ArgumentNullException.ThrowIfNull(manifest.Producer);
        ArgumentNullException.ThrowIfNull(manifest.Artifacts);

        var element = JsonSerializer.SerializeToElement(new
        {
            schema = "truth-release.v1",
            source = new
            {
                source_repo = manifest.Source.SourceRepo,
                source_commit = manifest.Source.SourceCommit,
                source_tree = manifest.Source.SourceTree,
            },
            trust = new
            {
                commit_on_protected_dev = manifest.Trust.CommitOnProtectedDev,
                required_checks = manifest.Trust.RequiredChecks.Select(static check => new
                {
                    name = check.Name,
                    conclusion = check.Conclusion,
                }),
                blessed_by = manifest.Trust.BlessedBy,
            },
            producer = new
            {
                package_repo = manifest.Producer.PackageRepo,
                package_commit = manifest.Producer.PackageCommit,
                read_only = manifest.Producer.ReadOnly,
            },
            artifacts = new
            {
                source_snapshot = Artifact(manifest.Artifacts.SourceSnapshot),
                truth_graph = Artifact(manifest.Artifacts.TruthGraph),
                raw_lean_report = Artifact(manifest.Artifacts.RawLeanReport),
                truth_export = Artifact(manifest.Artifacts.TruthExport),
                blueprint_index = Artifact(manifest.Artifacts.BlueprintIndex),
                frozen_ledger_head = Artifact(manifest.Artifacts.FrozenLedgerHead),
                residual_frontier = Artifact(manifest.Artifacts.ResidualFrontier),
            },
            sha256sums_digest = manifest.Sha256SumsDigest,
            produced_at = manifest.ProducedAt,
        }, SerializerOptions);
        var bytes = StructuredCanonicalWriter.WriteJson(element);
        _ = TruthReleaseManifestReader.Read(StrictUtf8.GetString(bytes.AsSpan()));
        return bytes;
    }

    private static object Artifact(TruthReleaseArtifact artifact)
    {
        ArgumentNullException.ThrowIfNull(artifact);
        return new
        {
            file = artifact.File,
            sha256 = artifact.Sha256,
        };
    }
}
