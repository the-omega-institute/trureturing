namespace StrataLint.ArchitectureTests;

internal static class ScribeTestMapTestFixture
{
    private const string ClaudeMarker = "__CLAUDE_MARKER__";

    internal static string RepositorySupport(string claudeMarker) => """
        enum RepositoryRootCriterion {
          ClaudeDirectoryNotFound,
          GlobalJsonAndBlueprintDirectoryNotFound,
        }
        readonly record struct RepositoryRoot(string FullPath);
        readonly record struct RepositoryRelativePath(string Value) {
          internal static RepositoryRelativePath Create(string value) => new(value);
        }
        readonly record struct RepositoryEntry(string FullPath);
        static class GitIndexRepositoryFiles {
          internal static IEnumerable<RepositoryEntry> EnumerateDeclared(string root, string prefix) => [];
        }
        class RepositoryAccessor {
          internal RepositoryRoot Root { get; } = new(string.Empty);
          internal static RepositoryAccessor Discover(RepositoryRootCriterion criterion) => new();
          internal string ReadAllText(RepositoryRelativePath path) => string.Empty;
          internal byte[] ReadAllBytes(RepositoryRelativePath path) => [];
          internal bool FileExists(RepositoryRelativePath path) => false;
          internal void CopyTo(RepositoryRelativePath source, string? destination) { }
          internal IReadOnlyList<RepositoryRelativePath> EnumerateFiles(
            RepositoryRelativePath directory,
            string searchPattern) => [];
          private static bool Matches(string root, RepositoryRootCriterion criterion) => criterion switch {
            RepositoryRootCriterion.ClaudeDirectoryNotFound => __CLAUDE_MARKER__,
            RepositoryRootCriterion.GlobalJsonAndBlueprintDirectoryNotFound =>
              File.Exists(Path.Combine(root, "global.json")) && Directory.Exists(Path.Combine(root, "Blueprint")),
            _ => false,
          };
        }
        """.Replace(ClaudeMarker, claudeMarker, StringComparison.Ordinal);
}
