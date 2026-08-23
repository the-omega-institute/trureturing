using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Cli;

internal static class SourceSnapshotAssembler
{
    internal static SourceSnapshotModel Assemble(
        RepositorySnapshot snapshot,
        FrozenRevisionIdentity identity,
        string sourceRepository,
        string producerPackageCommit,
        ImmutableArray<byte> truthGraphBytes,
        ImmutableArray<byte> rawLeanReportBytes,
        ImmutableArray<byte> dagMarkdownBytes,
        ImmutableArray<byte> residualFrontierBytes,
        ImmutableArray<byte> truthExportBytes,
        ImmutableArray<byte> frozenLedgerHeadBytes,
        int frozenLedgerSequence)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(identity);
        ArgumentException.ThrowIfNullOrWhiteSpace(sourceRepository);
        ArgumentException.ThrowIfNullOrWhiteSpace(producerPackageCommit);

        return new SourceSnapshotModel(
            "source-snapshot.v1",
            sourceRepository,
            identity.Revision,
            Bare(identity.TreeOid),
            LeanToolchain(snapshot),
            MathlibRevision(snapshot),
            producerPackageCommit,
            Digest(truthGraphBytes),
            Digest(rawLeanReportBytes),
            Digest(dagMarkdownBytes),
            Digest(residualFrontierBytes),
            Digest(truthExportBytes),
            Digest(frozenLedgerHeadBytes),
            frozenLedgerSequence);
    }

    private static string LeanToolchain(RepositorySnapshot snapshot)
    {
        var text = RequiredFile(snapshot, "lean-toolchain").Text;
        if (text.Contains('\r', StringComparison.Ordinal))
        {
            throw new FormatException("lean-toolchain contains CR bytes.");
        }

        var value = text.EndsWith('\n') ? text[..^1] : text;
        if (string.IsNullOrWhiteSpace(value) || value.Contains('\n', StringComparison.Ordinal))
        {
            throw new FormatException("lean-toolchain must contain exactly one non-empty line.");
        }

        return value;
    }

    private static string MathlibRevision(RepositorySnapshot snapshot)
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
        snapshot.TryGetFile(path, out var file)
            ? file
            : throw new FormatException($"immutable revision is missing {path}.");

    private static string Digest(ImmutableArray<byte> bytes) =>
        "sha256:" + Sha256Sums.HashHex(bytes.AsSpan());

    private static string Bare(string taggedOid)
    {
        var separator = taggedOid.IndexOf(':', StringComparison.Ordinal);
        return separator < 0 ? taggedOid : taggedOid[(separator + 1)..];
    }
}
