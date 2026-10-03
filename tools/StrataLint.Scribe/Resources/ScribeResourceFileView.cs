using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Scribe;

/// <summary>Repository-relative definition paths and file bytes; null denotes an absent file.</summary>
public interface IScribeResourceFileView
{
    IEnumerable<string> EnumerateDefinitionPaths();
    ImmutableArray<byte>? ReadBytes(string relativePath);
}

public sealed class WorkingTreeScribeResourceFileView : IScribeResourceFileView
{
    private readonly string root;

    public WorkingTreeScribeResourceFileView(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        root = Path.GetFullPath(repositoryRoot);
    }

    public IEnumerable<string> EnumerateDefinitionPaths() =>
        Directory.EnumerateFiles(Path.Combine(root, "Blueprint"), "*.scribe.cs", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(root, path).Replace('\\', '/'));

    public ImmutableArray<byte>? ReadBytes(string relativePath)
    {
        var path = Path.Combine(root, relativePath.Replace('/', Path.DirectorySeparatorChar));
        return File.Exists(path) ? ImmutableArray.CreateRange(File.ReadAllBytes(path)) : null;
    }
}

public sealed class SnapshotScribeResourceFileView : IScribeResourceFileView
{
    private readonly RepositorySnapshot snapshot;

    public SnapshotScribeResourceFileView(RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        this.snapshot = snapshot;
    }

    public IEnumerable<string> EnumerateDefinitionPaths() => snapshot.Files.Keys
        .Select(path => path.Value)
        .Where(path => path.StartsWith("Blueprint/", StringComparison.Ordinal)
            && path.EndsWith(".scribe.cs", StringComparison.Ordinal));

    public ImmutableArray<byte>? ReadBytes(string relativePath) =>
        snapshot.TryGetFile(relativePath, out var file) ? file.RawBytes : null;
}
