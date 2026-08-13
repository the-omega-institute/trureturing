using System.Collections.Immutable;
using System.Diagnostics.CodeAnalysis;
using System.Text;
using Dunet;

namespace StrataLint.Engine;

public sealed record RawRepositoryEntry(string Path, ImmutableArray<byte> Bytes)
{
    public static RawRepositoryEntry FromText(string path, string text) =>
        new(path, ImmutableArray.CreateRange(new UTF8Encoding(false, true).GetBytes(text)));
}

public sealed class RawRepositorySnapshot
{
    private RawRepositorySnapshot(ImmutableArray<RawRepositoryEntry> entries) => Entries = entries;

    public ImmutableArray<RawRepositoryEntry> Entries { get; }

    public static RawRepositorySnapshot Create(IEnumerable<RawRepositoryEntry> entries)
    {
        ArgumentNullException.ThrowIfNull(entries);
        return new RawRepositorySnapshot(entries.ToImmutableArray());
    }
}

public sealed class RepositoryFile
{
    internal RepositoryFile(
        RepoPath path,
        ImmutableArray<byte> rawBytes,
        string text,
        bool isOpaque = false)
    {
        Path = path;
        RawBytes = rawBytes;
        Text = text;
        IsOpaque = isOpaque;
        HasBom = text.StartsWith('\uFEFF');
        HasCarriageReturn = text.Contains('\r');
        HasTrailingWhitespace = text
            .Split('\n')
            .Any(static line => line.EndsWith(' ') || line.EndsWith('\t') || line.EndsWith('\r'));
    }

    public RepoPath Path { get; }

    public ImmutableArray<byte> RawBytes { get; }

    public string Text { get; }

    public bool IsOpaque { get; }

    public bool HasBom { get; }

    public bool HasCarriageReturn { get; }

    public bool HasTrailingWhitespace { get; }
}

public sealed class RepositorySnapshot
{
    private RepositorySnapshot(ImmutableDictionary<RepoPath, RepositoryFile> files) => Files = files;

    public ImmutableDictionary<RepoPath, RepositoryFile> Files { get; }

    internal static RepositorySnapshot Create(ImmutableDictionary<RepoPath, RepositoryFile> files) =>
        new(files);

    public bool TryGetFile(string path, [NotNullWhen(true)] out RepositoryFile? file)
    {
        if (RepoPath.TryCreate(path, out var repoPath) && Files.TryGetValue(repoPath, out file))
        {
            return true;
        }

        file = null;
        return false;
    }
}

[Union(EnableImplicitConversions = false)]
public partial record SnapshotDecodeOutcome
{
    public partial record Decoded(RepositorySnapshot Snapshot);

    public partial record InfrastructureFailure(string Message);
}

public static class SnapshotDecoder
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    public static SnapshotDecodeOutcome Decode(RawRepositorySnapshot raw)
    {
        ArgumentNullException.ThrowIfNull(raw);
        try
        {
            var builder = ImmutableDictionary.CreateBuilder<RepoPath, RepositoryFile>();
            var folded = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
            foreach (var entry in raw.Entries)
            {
                if (!RepoPath.TryCreate(entry.Path, out var path))
                {
                    throw new FormatException($"Repository path is invalid: {entry.Path}.");
                }

                if (!folded.Add(path.Value) || builder.ContainsKey(path))
                {
                    throw new FormatException($"Repository path is duplicated or case-colliding: {path.Value}.");
                }

                var isOpaque = DigestionOpaquePathPolicy.IsOpaque(path);
                var text = string.Empty;
                if (!isOpaque)
                {
                    try
                    {
                        text = StrictUtf8.GetString(entry.Bytes.AsSpan());
                    }
                    catch (DecoderFallbackException exception)
                    {
                        throw new FormatException(
                            $"Repository file must be strict UTF-8: {path.Value}.",
                            exception);
                    }
                }

                builder.Add(path, new RepositoryFile(path, entry.Bytes, text, isOpaque));
            }

            return new SnapshotDecodeOutcome.Decoded(RepositorySnapshot.Create(builder.ToImmutable()));
        }
        catch (FormatException exception)
        {
            return new SnapshotDecodeOutcome.InfrastructureFailure(exception.Message);
        }
    }
}
