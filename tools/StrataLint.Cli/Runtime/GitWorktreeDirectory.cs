namespace StrataLint.Cli;

internal static class GitWorktreeDirectory
{
    internal static string? Read(string repositoryRoot)
    {
        var dotGit = ResolvePath(repositoryRoot, null);
        if (Directory.Exists(dotGit)) return dotGit;
        if (!File.Exists(dotGit)) return null;

        var directory = ResolvePath(repositoryRoot, File.ReadAllText(dotGit));
        if (!Directory.Exists(directory)) throw new IOException("git metadata is absent");
        return directory;
    }

    internal static string ResolvePath(string repositoryRoot, string? pointer)
    {
        var root = Path.GetFullPath(repositoryRoot);
        if (pointer is null) return Path.Combine(root, ".git");

        pointer = pointer.Trim();
        const string prefix = "gitdir: ";
        if (!pointer.StartsWith(prefix, StringComparison.Ordinal))
            throw new IOException("invalid git directory pointer");
        return Path.GetFullPath(pointer[prefix.Length..], root);
    }
}
