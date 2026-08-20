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
/// Fail-closed reader for <c>release-manifest.v1.json</c>. It enforces the truth-release.v1 schema shape
/// exactly: the schema tag, the required fields and their patterns, <c>additionalProperties:false</c> on
/// every object, <c>producer.read_only == true</c>, and exactly the three named required checks each with
/// conclusion "success". It never repairs or defaults a malformed manifest. Shape only — it does NOT judge
/// provenance (that a commit is really on protected dev, that the checks are really green); that is
/// re-established independently against GitHub.
/// </summary>
public static class TruthReleaseManifestReader
{
    private static readonly ImmutableArray<string> RootKeys = ImmutableArray.Create(
        "schema", "source", "trust", "producer", "artifacts", "sha256sums_digest", "produced_at");

    private static readonly ImmutableArray<string> SourceKeys = ImmutableArray.Create(
        "source_repo", "source_commit", "source_tree");

    private static readonly ImmutableArray<string> TrustRequiredKeys = ImmutableArray.Create(
        "commit_on_protected_dev", "required_checks");

    private static readonly ImmutableArray<string> TrustOptionalKeys = ImmutableArray.Create("blessed_by");

    private static readonly ImmutableArray<string> ProducerKeys = ImmutableArray.Create(
        "package_repo", "package_commit", "read_only");

    private static readonly ImmutableArray<string> CheckKeys = ImmutableArray.Create("name", "conclusion");

    private static readonly ImmutableArray<string> ArtifactObjectKeys = ImmutableArray.Create("file", "sha256");

    private static readonly ImmutableArray<string> ArtifactKeys = ImmutableArray.Create(
        "source_snapshot", "truth_graph", "raw_lean_report", "declarations",
        "blueprint_index", "frozen_ledger_head", "residual_frontier");

    private static readonly ImmutableArray<string> RequiredCheckNames = ImmutableArray.Create(
        "Candidate harness engineering checks",
        "Canonical Lean report production",
        "Content-addressed dev baseline admission");

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
            RequireKeys(root, RootKeys, ImmutableArray<string>.Empty, "release-manifest");
            if (RequireString(root, "schema") != "truth-release.v1")
            {
                throw new FormatException("release-manifest schema tag is not truth-release.v1.");
            }

            var sourceElement = RequireObject(RequireProperty(root, "source"), "source");
            RequireKeys(sourceElement, SourceKeys, ImmutableArray<string>.Empty, "source");
            var source = new TruthReleaseSource(
                RequireString(sourceElement, "source_repo"),
                RequireHex(sourceElement, "source_commit", 40),
                RequireHex(sourceElement, "source_tree", 40));

            var trustElement = RequireObject(RequireProperty(root, "trust"), "trust");
            RequireKeys(trustElement, TrustRequiredKeys, TrustOptionalKeys, "trust");
            var trust = new TruthReleaseTrust(
                RequireBool(trustElement, "commit_on_protected_dev"),
                ReadRequiredChecks(trustElement),
                OptionalString(trustElement, "blessed_by"));

            var producerElement = RequireObject(RequireProperty(root, "producer"), "producer");
            RequireKeys(producerElement, ProducerKeys, ImmutableArray<string>.Empty, "producer");
            if (!RequireBool(producerElement, "read_only"))
            {
                throw new FormatException("producer.read_only must be true.");
            }

            var producer = new TruthReleaseProducer(
                RequireString(producerElement, "package_repo"),
                RequireHex(producerElement, "package_commit", 40),
                ReadOnly: true);

            var artifactsElement = RequireObject(RequireProperty(root, "artifacts"), "artifacts");
            RequireKeys(artifactsElement, ArtifactKeys, ImmutableArray<string>.Empty, "artifacts");
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

    private static ImmutableArray<TruthReleaseRequiredCheck> ReadRequiredChecks(JsonElement trust)
    {
        var checks = ImmutableArray.CreateBuilder<TruthReleaseRequiredCheck>();
        var names = new HashSet<string>(StringComparer.Ordinal);
        foreach (var checkElement in RequireArray(trust, "required_checks"))
        {
            var checkObject = RequireObject(checkElement, "required_checks[]");
            RequireKeys(checkObject, CheckKeys, ImmutableArray<string>.Empty, "required_checks[]");
            var name = RequireString(checkObject, "name");
            var conclusion = RequireString(checkObject, "conclusion");
            if (conclusion != "success")
            {
                throw new FormatException($"required check '{name}' does not record conclusion 'success'.");
            }

            if (!names.Add(name))
            {
                throw new FormatException($"required check '{name}' is listed more than once.");
            }

            checks.Add(new TruthReleaseRequiredCheck(name, conclusion));
        }

        if (!names.SetEquals(RequiredCheckNames))
        {
            throw new FormatException("required_checks is not exactly the three named protected-dev checks.");
        }

        return checks.ToImmutable();
    }

    private static TruthReleaseArtifact ReadArtifact(JsonElement artifacts, string name)
    {
        var element = RequireObject(RequireProperty(artifacts, name), name);
        RequireKeys(element, ArtifactObjectKeys, ImmutableArray<string>.Empty, name);
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

    private static string? OptionalString(JsonElement parent, string name)
    {
        if (!parent.TryGetProperty(name, out var value))
        {
            return null;
        }

        return value.ValueKind == JsonValueKind.String
            ? value.GetString()
            : throw new FormatException($"release-manifest field '{name}' is present but is not a string.");
    }

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

    private static void RequireKeys(
        JsonElement element,
        ImmutableArray<string> required,
        ImmutableArray<string> optional,
        string label)
    {
        var present = new HashSet<string>(StringComparer.Ordinal);
        foreach (var property in element.EnumerateObject())
        {
            // JsonDocument keeps duplicate property names; a fail-closed reader must reject the
            // ambiguity rather than silently collapse to whichever occurrence TryGetProperty returns.
            if (!present.Add(property.Name))
            {
                throw new FormatException($"release-manifest '{label}' has a duplicate '{property.Name}' field.");
            }
        }

        foreach (var key in required)
        {
            if (!present.Remove(key))
            {
                throw new FormatException($"release-manifest '{label}' is missing required entry '{key}'.");
            }
        }

        foreach (var key in optional)
        {
            present.Remove(key);
        }

        if (present.Count > 0)
        {
            throw new FormatException($"release-manifest '{label}' has unexpected fields beyond the schema.");
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
