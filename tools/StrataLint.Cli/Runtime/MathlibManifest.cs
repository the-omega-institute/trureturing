using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class MathlibManifest
{
    internal static string Revision(RepositorySnapshot snapshot)
    {
        try
        {
            using var document = JsonDocument.Parse(RequiredFile(snapshot, "lake-manifest.json").Text);
            if (!document.RootElement.TryGetProperty("packages", out var packages)
                || packages.ValueKind != JsonValueKind.Array)
            {
                throw new FormatException("lake-manifest.json packages must be an array.");
            }

            var matches = packages.EnumerateArray()
                .Where(static package => package.ValueKind == JsonValueKind.Object
                    && package.TryGetProperty("name", out var name)
                    && name.ValueKind == JsonValueKind.String
                    && name.GetString() == "mathlib")
                .ToArray();
            if (matches.Length != 1
                || !matches[0].TryGetProperty("rev", out var revision)
                || revision.ValueKind != JsonValueKind.String
                || string.IsNullOrWhiteSpace(revision.GetString()))
            {
                throw new FormatException(
                    "lake-manifest.json must contain exactly one mathlib package with a rev.");
            }

            return revision.GetString()!;
        }
        catch (JsonException exception)
        {
            throw new FormatException("lake-manifest.json is invalid JSON.", exception);
        }
    }

    private static RepositoryFile RequiredFile(RepositorySnapshot snapshot, string path) =>
        snapshot.TryGetFile(path, out var file) ? file : throw new FormatException($"immutable revision is missing {path}.");
}
