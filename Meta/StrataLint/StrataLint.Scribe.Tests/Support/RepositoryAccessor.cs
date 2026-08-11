namespace StrataLint.Scribe.Tests;

internal enum RepositoryRootCriterion
{
    GlobalJsonAndBlueprintDirectoryNotFound,
    GlobalJsonAndBlueprintInvalidOperation,
    GlobalJsonAndLibraryInvalidOperation,
    ClaudeDirectoryNotFound,
    LakefileInvalidOperation,
    FileMapDirectoryNotFound,
    ValuesDataDirectoryNotFound,
    ValuesProducerDirectoryNotFound,
}

internal readonly record struct RepositoryRoot
{
    internal RepositoryRoot(string fullPath) => FullPath = fullPath;

    internal string FullPath { get; }
}

internal readonly record struct RepositoryRelativePath
{
    private RepositoryRelativePath(string value) => Value = value;

    internal string Value { get; }

    internal static RepositoryRelativePath Create(string value)
    {
        if (string.IsNullOrWhiteSpace(value)
            || Path.IsPathRooted(value)
            || value.Split('/', '\\').Any(static segment => segment is "" or "." or ".."))
        {
            throw new ArgumentException("repository path must be a normalized relative path", nameof(value));
        }

        return new RepositoryRelativePath(value.Replace('\\', '/'));
    }

    public override string ToString() => Value;
}

internal sealed class RepositoryAccessor
{
    private readonly HashSet<RepositoryRelativePath> accessedPaths = [];

    private RepositoryAccessor(RepositoryRoot root) => Root = root;

    internal RepositoryRoot Root { get; }

    internal IReadOnlySet<RepositoryRelativePath> AccessedPaths => accessedPaths;

    internal static RepositoryAccessor Discover(RepositoryRootCriterion criterion) =>
        Discover(AppContext.BaseDirectory, criterion);

    internal static RepositoryAccessor Discover(
        string startDirectory,
        RepositoryRootCriterion criterion)
    {
        for (var current = new DirectoryInfo(startDirectory);
             current is not null;
             current = current.Parent)
        {
            if (Matches(current.FullName, criterion))
            {
                return new RepositoryAccessor(new RepositoryRoot(current.FullName));
            }
        }

        throw CreateFailure(criterion);
    }

    internal string ReadAllText(RepositoryRelativePath path) =>
        File.ReadAllText(RecordAndResolve(path));

    internal byte[] ReadAllBytes(RepositoryRelativePath path) =>
        File.ReadAllBytes(RecordAndResolve(path));

    internal bool FileExists(RepositoryRelativePath path) => File.Exists(RecordAndResolve(path));

    internal string GetFullPath(RepositoryRelativePath path) => RecordAndResolve(path);

    internal void CopyTo(
        RepositoryRelativePath source,
        string destination,
        bool overwrite = false) =>
        File.Copy(RecordAndResolve(source), destination, overwrite);

    internal IReadOnlyList<RepositoryRelativePath> EnumerateFiles(
        RepositoryRelativePath directory,
        string searchPattern)
    {
        accessedPaths.Add(directory);
        return Directory
            .EnumerateFiles(Resolve(directory), searchPattern, SearchOption.AllDirectories)
            .Select(path => RepositoryRelativePath.Create(Path.GetRelativePath(Root.FullPath, path)))
            .ToArray();
    }

    private string Resolve(RepositoryRelativePath path) =>
        Path.Combine(Root.FullPath, path.Value.Replace('/', Path.DirectorySeparatorChar));

    private string RecordAndResolve(RepositoryRelativePath path)
    {
        accessedPaths.Add(path);
        return Resolve(path);
    }

    private static bool Matches(string root, RepositoryRootCriterion criterion) => criterion switch
    {
        RepositoryRootCriterion.GlobalJsonAndBlueprintDirectoryNotFound
            or RepositoryRootCriterion.GlobalJsonAndBlueprintInvalidOperation =>
            File.Exists(Path.Combine(root, "global.json"))
            && Directory.Exists(Path.Combine(root, "Blueprint")),
        RepositoryRootCriterion.GlobalJsonAndLibraryInvalidOperation =>
            File.Exists(Path.Combine(root, "global.json"))
            && Directory.Exists(Path.Combine(root, "Library")),
        RepositoryRootCriterion.ClaudeDirectoryNotFound =>
            File.Exists(Path.Combine(root, "CLAUDE.md")),
        RepositoryRootCriterion.LakefileInvalidOperation =>
            File.Exists(Path.Combine(root, "lakefile.toml")),
        RepositoryRootCriterion.FileMapDirectoryNotFound =>
            File.Exists(Path.Combine(root, "Meta", "FILEMAP.toml")),
        RepositoryRootCriterion.ValuesDataDirectoryNotFound =>
            File.Exists(Path.Combine(root, "Golden", "values-kernels.toml")),
        RepositoryRootCriterion.ValuesProducerDirectoryNotFound =>
            File.Exists(Path.Combine(root, "D5", "X_Frontier", "ValuesProducer.lean")),
        _ => throw new ArgumentOutOfRangeException(nameof(criterion)),
    };

    private static Exception CreateFailure(RepositoryRootCriterion criterion) => criterion switch
    {
        RepositoryRootCriterion.GlobalJsonAndBlueprintInvalidOperation
            or RepositoryRootCriterion.GlobalJsonAndLibraryInvalidOperation
            or RepositoryRootCriterion.LakefileInvalidOperation =>
            new InvalidOperationException("repository root was not found above the test base directory"),
        _ => new DirectoryNotFoundException("Could not locate the repository root."),
    };
}
