using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Cli;

internal static class RunLocalSnapshotOverlay
{
    internal static RawRepositorySnapshot Apply(
        RawRepositorySnapshot snapshot,
        string outputRoot,
        string expectedRequestSha256,
        IReadOnlyList<RunArtifactInventoryItem> inventory,
        IReadOnlySet<string>? pathsToOverlay = null,
        bool onlyWhenMissing = false)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        var verified = RunHandleConsumer.Consume(outputRoot, expectedRequestSha256, inventory);
        if (verified.ExitCode != 0)
        {
            throw new InvalidOperationException(
                "RUN_LOCAL_RECEIPT_INVALID " + verified.Diagnostic.Trim());
        }

        using var handle = RunHandleJson.ParseCanonical(
            File.ReadAllBytes(Path.Combine(outputRoot, "handle.json")));
        var runId = handle.RootElement.GetProperty("run_id").GetString()!;
        var existing = snapshot.Entries.Select(static entry => entry.Path)
            .ToHashSet(StringComparer.Ordinal);
        var replacements = inventory
            .Where(item => pathsToOverlay is null || pathsToOverlay.Contains(item.Path))
            .Where(item => !onlyWhenMissing || !existing.Contains(item.Path))
            .ToDictionary(
            static item => item.Path,
            item => new RawRepositoryEntry(
                item.Path,
                ImmutableArray.CreateRange(File.ReadAllBytes(
                    RunPath.ResolveContained(
                        Path.Combine(outputRoot, runId),
                        item.Path,
                        requireExists: true)))),
            StringComparer.Ordinal);
        return RawRepositorySnapshot.Create(
            snapshot.Entries
                .Where(entry => !replacements.ContainsKey(entry.Path))
                .Concat(replacements.Values)
                .OrderBy(static entry => entry.Path, StringComparer.Ordinal));
    }

    internal static RawRepositorySnapshot ApplyFromEnvironment(
        RawRepositorySnapshot snapshot,
        string repositoryRoot)
    {
        var outputRoot = Environment.GetEnvironmentVariable("STRATALINT_RUN_RECEIPT_ROOT");
        if (string.IsNullOrWhiteSpace(outputRoot) || !Path.IsPathFullyQualified(outputRoot))
        {
            throw new InvalidOperationException(
                "RUN_LOCAL_RECEIPT_MISSING STRATALINT_RUN_RECEIPT_ROOT must name an absolute verified run-handle root");
        }
        return ApplyFromReceipt(snapshot, repositoryRoot, outputRoot);
    }

    internal static RawRepositorySnapshot ApplyFromReceipt(
        RawRepositorySnapshot snapshot,
        string repositoryRoot,
        string outputRoot)
    {
        var manifest = FileMapLoader.LoadRepository(repositoryRoot);
        var inventory = manifest.Entries
            .Where(static entry => entry.Kind is FileMapKind.Generated
                && entry.RuntimeDisposition == "run-local"
                && entry.ArtifactId != "none")
            .Select(static entry => new RunArtifactInventoryItem(
                entry.ArtifactId, entry.Pattern, entry.Mode!))
            .OrderBy(static entry => entry.Path, StringComparer.Ordinal)
            .ToArray();
        if (inventory.Length == 0)
        {
            return snapshot;
        }

        if (string.IsNullOrWhiteSpace(outputRoot) || !Path.IsPathFullyQualified(outputRoot))
        {
            throw new InvalidOperationException(
                "RUN_LOCAL_RECEIPT_MISSING STRATALINT_RUN_RECEIPT_ROOT must name an absolute verified run-handle root");
        }

        try
        {
            using var handle = RunHandleJson.ParseCanonical(
                File.ReadAllBytes(Path.Combine(outputRoot, "handle.json")));
            var expected = handle.RootElement.GetProperty("request_sha256").GetString()!;
            var consumerPaths = new HashSet<string>(StringComparer.Ordinal)
            {
                ValuesProjectionLoader.RelativePath,
                AnchorCatalogLoader.RelativePath,
                ScribeEmissionAttestation.RelativePath,
            };
            return Apply(snapshot, outputRoot, expected, inventory, consumerPaths, onlyWhenMissing: true);
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException
            or FormatException or JsonException or InvalidOperationException)
        {
            throw new InvalidOperationException(
                "RUN_LOCAL_RECEIPT_INVALID " + exception.Message,
                exception);
        }
    }
}
