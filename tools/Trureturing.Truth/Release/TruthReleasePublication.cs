using System.Collections.Immutable;
using System.Text;
using System.Text.Json;

namespace Trureturing.Truth;

/// <summary>
/// The immutable downstream coordinate for one already-assembled truth-release bundle.
/// The coordinate contains no transport locator or downstream business semantics. Deployment
/// resolves <see cref="BundleRef"/> to physical bytes and chooses how to deliver this record.
/// </summary>
public sealed record TruthReleasePublication(
    string ReleaseDigest,
    string BundleRef,
    string SourceCommit,
    string SourceTree,
    string ProducerCommit);

/// <summary>
/// Fail-closed reader for <c>truth-release-publication.v1</c>. It requires the exact field set,
/// rejects duplicate and unknown properties, validates every content and Git identity, and requires
/// <c>bundle_ref == release_digest</c> so the downstream coordinate cannot be rebound to other bytes.
/// </summary>
public static class TruthReleasePublicationReader
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    private static readonly ImmutableArray<string> Properties = ImmutableArray.Create(
        "bundle_ref",
        "producer_commit",
        "release_digest",
        "schema",
        "source_commit",
        "source_tree");

    public static TruthReleasePublication Read(ReadOnlySpan<byte> bytes)
    {
        try
        {
            return Read(StrictUtf8.GetString(bytes));
        }
        catch (DecoderFallbackException exception)
        {
            throw new FormatException("truth-release-publication.v1 is not valid UTF-8.", exception);
        }
    }

    public static TruthReleasePublication Read(string json)
    {
        ArgumentNullException.ThrowIfNull(json);

        JsonDocument document;
        try
        {
            document = JsonDocument.Parse(json);
        }
        catch (JsonException exception)
        {
            throw new FormatException("truth-release-publication.v1 is not valid JSON.", exception);
        }

        using (document)
        {
            var root = document.RootElement;
            RequireProperties(root);
            if (RequireString(root, "schema") != "truth-release-publication.v1")
            {
                throw new FormatException(
                    "truth-release-publication schema tag is not truth-release-publication.v1.");
            }

            var releaseDigest = RequireDigest(root, "release_digest");
            var bundleRef = RequireDigest(root, "bundle_ref");
            if (!string.Equals(bundleRef, releaseDigest, StringComparison.Ordinal))
            {
                throw new FormatException(
                    "truth-release-publication bundle_ref must equal release_digest.");
            }

            var sourceCommit = RequireGitObjectId(root, "source_commit");
            var sourceTree = RequireGitObjectId(root, "source_tree");
            TruthExportValidation.RequireSameGitObjectFormat(sourceCommit, sourceTree);

            return new TruthReleasePublication(
                releaseDigest,
                bundleRef,
                sourceCommit,
                sourceTree,
                RequireGitObjectId(root, "producer_commit"));
        }
    }

    private static void RequireProperties(JsonElement root)
    {
        if (root.ValueKind != JsonValueKind.Object)
        {
            throw new FormatException("truth-release-publication must be an object.");
        }

        var actual = new HashSet<string>(StringComparer.Ordinal);
        foreach (var property in root.EnumerateObject())
        {
            if (!actual.Add(property.Name))
            {
                throw new FormatException(
                    $"truth-release-publication property '{property.Name}' is duplicated.");
            }
        }

        if (actual.Count != Properties.Length || !actual.SetEquals(Properties))
        {
            throw new FormatException(
                "truth-release-publication has missing or unexpected fields.");
        }
    }

    private static string RequireString(JsonElement root, string name) =>
        root.TryGetProperty(name, out var value) && value.ValueKind == JsonValueKind.String
            ? value.GetString()
                ?? throw new FormatException(
                    $"truth-release-publication field '{name}' is null.")
            : throw new FormatException(
                $"truth-release-publication field '{name}' must be a string.");

    private static string RequireDigest(JsonElement root, string name)
    {
        var value = RequireString(root, name);
        TruthExportValidation.RequireSha256Id(value, name);
        return value;
    }

    private static string RequireGitObjectId(JsonElement root, string name)
    {
        var value = RequireString(root, name);
        TruthExportValidation.RequireGitObjectId(value, name);
        return value;
    }
}

/// <summary>
/// Canonical writer for <c>truth-release-publication.v1</c>. The shared structured writer fixes
/// key order, spacing, UTF-8 encoding and the final LF. The strict reader validates the emitted bytes
/// before they leave this API.
/// </summary>
public static class TruthReleasePublicationJsonWriter
{
    public static ImmutableArray<byte> Write(TruthReleasePublication publication)
    {
        ArgumentNullException.ThrowIfNull(publication);
        var element = JsonSerializer.SerializeToElement(new
        {
            schema = "truth-release-publication.v1",
            release_digest = publication.ReleaseDigest,
            bundle_ref = publication.BundleRef,
            source_commit = publication.SourceCommit,
            source_tree = publication.SourceTree,
            producer_commit = publication.ProducerCommit,
        });
        var bytes = StructuredCanonicalWriter.WriteJson(element);
        if (TruthReleasePublicationReader.Read(bytes.AsSpan()) != publication)
        {
            throw new FormatException(
                "truth-release-publication writer did not preserve its input model.");
        }

        return bytes;
    }
}
