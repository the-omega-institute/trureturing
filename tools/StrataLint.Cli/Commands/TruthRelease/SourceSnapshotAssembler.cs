using System.Collections.Immutable;
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
            MathlibManifest.Revision(snapshot),
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
