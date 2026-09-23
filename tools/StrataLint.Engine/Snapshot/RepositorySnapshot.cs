using System.Collections.Immutable;
using System.Diagnostics.CodeAnalysis;
using System.Text;
using Dunet;

namespace StrataLint.Engine;

public sealed record RawRepositoryEntry(
    string Path,
    ImmutableArray<byte> Bytes,
    string? GitBlobOid = null)
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
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private readonly Lazy<string> text;

    internal RepositoryFile(
        RepoPath path,
        ImmutableArray<byte> rawBytes,
        string text,
        bool isOpaque = false,
        string? gitBlobOid = null)
    {
        Path = path;
        RawBytes = rawBytes;
        this.text = new(() => text);
        IsOpaque = isOpaque;
        GitBlobOid = gitBlobOid;
        HasBom = text.StartsWith('\uFEFF');
        HasCarriageReturn = text.Contains('\r');
        HasTrailingWhitespace = ContainsTrailingWhitespace(text.AsSpan());
    }

    // SnapshotDecoder validates UTF-8 eagerly; consumers materialize text only when needed.
    internal RepositoryFile(
        RepoPath path,
        ImmutableArray<byte> rawBytes,
        bool isOpaque,
        string? gitBlobOid)
    {
        Path = path;
        RawBytes = rawBytes;
        IsOpaque = isOpaque;
        GitBlobOid = gitBlobOid;
        text = new(() => IsOpaque ? string.Empty : StrictUtf8.GetString(RawBytes.AsSpan()));
        var bytes = isOpaque ? ReadOnlySpan<byte>.Empty : rawBytes.AsSpan();
        HasBom = bytes.Length >= 3 && bytes[0] == 0xef && bytes[1] == 0xbb && bytes[2] == 0xbf;
        HasCarriageReturn = bytes.Contains((byte)'\r');
        while (true)
        {
            var newline = bytes.IndexOf((byte)'\n');
            var length = newline < 0 ? bytes.Length : newline;
            if (length > 0 && bytes[length - 1] is (byte)' ' or (byte)'\t' or (byte)'\r')
            {
                HasTrailingWhitespace = true;
                break;
            }
            if (newline < 0) break;
            bytes = bytes[(newline + 1)..];
        }
    }

    private static bool ContainsTrailingWhitespace(ReadOnlySpan<char> remaining)
    {
        while (true)
        {
            var newline = remaining.IndexOf('\n');
            var length = newline < 0 ? remaining.Length : newline;
            if (length > 0 && remaining[length - 1] is ' ' or '\t' or '\r') return true;
            if (newline < 0) return false;
            remaining = remaining[(newline + 1)..];
        }
    }

    public RepoPath Path { get; }

    public ImmutableArray<byte> RawBytes { get; }

    public string Text => text.Value;

    public bool IsOpaque { get; }

    public string? GitBlobOid { get; }

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
                if (!isOpaque)
                {
                    try
                    {
                        _ = StrictUtf8.GetCharCount(entry.Bytes.AsSpan());
                    }
                    catch (DecoderFallbackException exception)
                    {
                        throw new FormatException(
                            $"Repository file must be strict UTF-8: {path.Value}.",
                            exception);
                    }
                }

                if (entry.GitBlobOid is not null && !FrozenHashSyntax.IsGitOid(entry.GitBlobOid))
                {
                    throw new FormatException(
                        $"Repository file has an invalid trusted Git blob identity: {path.Value}.");
                }

                builder.Add(path, new RepositoryFile(
                    path,
                    entry.Bytes,
                    isOpaque,
                    entry.GitBlobOid));
            }

            return new SnapshotDecodeOutcome.Decoded(RepositorySnapshot.Create(builder.ToImmutable()));
        }
        catch (FormatException exception)
        {
            return new SnapshotDecodeOutcome.InfrastructureFailure(exception.Message);
        }
    }
}
