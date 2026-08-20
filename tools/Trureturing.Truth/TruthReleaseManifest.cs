using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Text.Json;

namespace Trureturing.Truth;

/// <summary>One bundle artifact: its bundle-relative filename and its "sha256:&lt;64hex&gt;" digest.</summary>
public sealed record TruthReleaseArtifact(string File, string Sha256);

/// <summary>One of the three required GitHub check-runs a valid release must witness green.</summary>
public sealed record TruthReleaseRequiredCheck(string Name, string Conclusion);

/// <summary>The exact protected-dev commit the release derives from (read-only).</summary>
public sealed record TruthReleaseSource(string SourceRepo, string SourceCommit, string SourceTree);

/// <summary>
/// The producer's SELF-ASSERTED trust record — NOT independently authoritative. A consumer must
/// re-verify <see cref="CommitOnProtectedDev"/> and <see cref="RequiredChecks"/> against GitHub for
/// the exact commit and establish provenance by reproducing the bundle. <c>BlessedBy</c> is audit-only.
/// </summary>
public sealed record TruthReleaseTrust(
    bool CommitOnProtectedDev,
    ImmutableArray<TruthReleaseRequiredCheck> RequiredChecks,
    string? BlessedBy);

/// <summary>The package that assembled the bundle; it only packages base-owned outputs (read-only).</summary>
public sealed record TruthReleaseProducer(string PackageRepo, string PackageCommit, bool ReadOnly);

/// <summary>The seven required release artifacts, each a sibling file bound by SHA256SUMS.</summary>
public sealed record TruthReleaseArtifacts(
    TruthReleaseArtifact SourceSnapshot,
    TruthReleaseArtifact TruthGraph,
    TruthReleaseArtifact RawLeanReport,
    TruthReleaseArtifact Declarations,
    TruthReleaseArtifact BlueprintIndex,
    TruthReleaseArtifact FrozenLedgerHead,
    TruthReleaseArtifact ResidualFrontier);

/// <summary>
/// The parsed, shape-validated <c>release-manifest.v1.json</c> (schema "truth-release.v1"). This is a
/// plain READ model — parsing it proves nothing about provenance; it only records what the producer
/// listed. Authority still comes from independently re-deriving the bundle from <see cref="TruthReleaseSource"/>.
/// </summary>
public sealed record TruthReleaseManifest(
    TruthReleaseSource Source,
    TruthReleaseTrust Trust,
    TruthReleaseProducer Producer,
    TruthReleaseArtifacts Artifacts,
    string Sha256SumsDigest,
    string ProducedAt);

/// <summary>
/// Fail-closed reader for <c>release-manifest.v1.json</c>. Rejects any document that is not an exact
/// truth-release.v1 manifest: wrong schema tag, missing required field, a missing or extra artifact,
/// or a malformed commit / digest. It never repairs or defaults a malformed manifest. Structural only —
/// it does NOT judge provenance (that a commit is on protected dev, that the three checks are green);
/// those are re-established independently against GitHub, per the truth-release.v1 contract.
/// </summary>
public static class TruthReleaseManifestReader
{
    private static readonly ImmutableArray<string> ArtifactKeys = ImmutableArray.Create(
        "source_snapshot", "truth_graph", "raw_lean_report", "declarations",
        "blueprint_index", "frozen_ledger_head", "residual_frontier");

    public static TruthReleaseManifest Read(string json)
    {
        ArgumentNullException.ThrowIfNull(json);

        JsonDocument document;
        try
        {
            document = JsonDocument.Parse(json);
        }
        catch (JsonException exception)
        {
            throw new FormatException("release-manifest.v1 is not valid JSON.", exception);
        }

        using (document)
        {
            var root = RequireObject(document.RootElement, "release-manifest");
            if (RequireString(root, "schema") != "truth-release.v1")
            {
                throw new FormatException("release-manifest schema tag is not truth-release.v1.");
            }

            var sourceElement = RequireObject(RequireProperty(root, "source"), "source");
            var source = new TruthReleaseSource(
                RequireString(sourceElement, "source_repo"),
                RequireHex(sourceElement, "source_commit", 40),
                RequireHex(sourceElement, "source_tree", 40));

            var trustElement = RequireObject(RequireProperty(root, "trust"), "trust");
            var checks = ImmutableArray.CreateBuilder<TruthReleaseRequiredCheck>();
            foreach (var checkElement in RequireArray(trustElement, "required_checks"))
            {
                var checkObject = RequireObject(checkElement, "required_checks[]");
                checks.Add(new TruthReleaseRequiredCheck(
                    RequireString(checkObject, "name"),
                    RequireString(checkObject, "conclusion")));
            }

            var trust = new TruthReleaseTrust(
                RequireBool(trustElement, "commit_on_protected_dev"),
                checks.ToImmutable(),
                OptionalString(trustElement, "blessed_by"));

            var producerElement = RequireObject(RequireProperty(root, "producer"), "producer");
            var producer = new TruthReleaseProducer(
                RequireString(producerElement, "package_repo"),
                RequireHex(producerElement, "package_commit", 40),
                RequireBool(producerElement, "read_only"));

            var artifactsElement = RequireObject(RequireProperty(root, "artifacts"), "artifacts");
            RequireExactKeys(artifactsElement, ArtifactKeys, "artifacts");
            var artifacts = new TruthReleaseArtifacts(
                ReadArtifact(artifactsElement, "source_snapshot"),
                ReadArtifact(artifactsElement, "truth_graph"),
                ReadArtifact(artifactsElement, "raw_lean_report"),
                ReadArtifact(artifactsElement, "declarations"),
                ReadArtifact(artifactsElement, "blueprint_index"),
                ReadArtifact(artifactsElement, "frozen_ledger_head"),
                ReadArtifact(artifactsElement, "residual_frontier"));

            return new TruthReleaseManifest(
                source,
                trust,
                producer,
                artifacts,
                RequireDigest(root, "sha256sums_digest"),
                RequireString(root, "produced_at"));
        }
    }

    private static TruthReleaseArtifact ReadArtifact(JsonElement artifacts, string name)
    {
        var element = RequireObject(RequireProperty(artifacts, name), name);
        return new TruthReleaseArtifact(
            RequireString(element, "file"),
            RequireDigest(element, "sha256"));
    }

    private static JsonElement RequireProperty(JsonElement parent, string name) =>
        parent.TryGetProperty(name, out var value)
            ? value
            : throw new FormatException($"release-manifest is missing required field '{name}'.");

    private static JsonElement RequireObject(JsonElement value, string label) =>
        value.ValueKind == JsonValueKind.Object
            ? value
            : throw new FormatException($"release-manifest field '{label}' is not an object.");

    private static string RequireString(JsonElement parent, string name)
    {
        var value = RequireProperty(parent, name);
        return value.ValueKind == JsonValueKind.String
            ? value.GetString()!
            : throw new FormatException($"release-manifest field '{name}' is not a string.");
    }

    private static string? OptionalString(JsonElement parent, string name) =>
        parent.TryGetProperty(name, out var value) && value.ValueKind == JsonValueKind.String
            ? value.GetString()
            : null;

    private static bool RequireBool(JsonElement parent, string name)
    {
        var value = RequireProperty(parent, name);
        return value.ValueKind switch
        {
            JsonValueKind.True => true,
            JsonValueKind.False => false,
            _ => throw new FormatException($"release-manifest field '{name}' is not a boolean."),
        };
    }

    private static JsonElement.ArrayEnumerator RequireArray(JsonElement parent, string name)
    {
        var value = RequireProperty(parent, name);
        return value.ValueKind == JsonValueKind.Array
            ? value.EnumerateArray()
            : throw new FormatException($"release-manifest field '{name}' is not an array.");
    }

    private static string RequireHex(JsonElement parent, string name, int length)
    {
        var value = RequireString(parent, name);
        return IsHex(value, length)
            ? value
            : throw new FormatException($"release-manifest field '{name}' is not {length} lowercase hex chars.");
    }

    private static string RequireDigest(JsonElement parent, string name)
    {
        var value = RequireString(parent, name);
        const string prefix = "sha256:";
        return value.StartsWith(prefix, StringComparison.Ordinal) && IsHex(value.AsSpan(prefix.Length), 64)
            ? value
            : throw new FormatException($"release-manifest field '{name}' is not a 'sha256:<64hex>' digest.");
    }

    private static void RequireExactKeys(JsonElement element, ImmutableArray<string> required, string label)
    {
        var present = new HashSet<string>(StringComparer.Ordinal);
        foreach (var property in element.EnumerateObject())
        {
            present.Add(property.Name);
        }

        foreach (var key in required)
        {
            if (!present.Remove(key))
            {
                throw new FormatException($"release-manifest '{label}' is missing required entry '{key}'.");
            }
        }

        if (present.Count > 0)
        {
            throw new FormatException($"release-manifest '{label}' has unexpected entries beyond the required set.");
        }
    }

    private static bool IsHex(ReadOnlySpan<char> value, int length)
    {
        if (value.Length != length)
        {
            return false;
        }

        foreach (var character in value)
        {
            var isHex = character is (>= '0' and <= '9') or (>= 'a' and <= 'f');
            if (!isHex)
            {
                return false;
            }
        }

        return true;
    }
}
