using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class LeanSourceContextArtifact
{
    internal static LeanSourceContextInput ReadBundle(string report, RepositorySnapshot current,
        RepositorySnapshot protectedBase) => File.Exists(report + ".source-context.json")
        ? LeanSourceContextInput.Load(File.ReadAllBytes(report + ".source-context.json"), current, protectedBase)
        : LeanSourceContextInput.Empty;
}
