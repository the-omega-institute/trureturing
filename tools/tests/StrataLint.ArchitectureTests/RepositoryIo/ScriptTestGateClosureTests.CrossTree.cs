using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

public sealed partial class ScriptTestGateClosureTests
{
    [Fact]
    public void CrossTreeEnvironmentInitializerMatchesSameTreeVerdict()
    {
        // Base f45173ac8090's equivalent same-tree fixture returns a closure: an
        // Environment call is neither FindRoot nor the syntactic Root.FullPath pattern.
        // The oracle adds no consumed path. Pin the complete closure independently.
        foreach (var crossTree in new[] { false, true })
        {
            var closure = Derive(RootInitializerSnapshot(
                "System.Environment.GetEnvironmentVariable(\"SCRIPT_GATE_ROOT\")!", crossTree), []);
            Assert.Equal(new[] {
                "Directory.Build.props", "Directory.Packages.props", "global.json",
                EngineProject, "tools/StrataLint.Engine/packages.lock.json",
                EngineeringScopeProject, "tools/StrataLint.EngineeringScope/packages.lock.json",
                TruthProject, "tools/Trureturing.Truth/packages.lock.json",
                ScriptTestsProject, "tools/tests/StrataLint.ScriptTests/packages.lock.json",
                TestSupportProject, "tools/tests/StrataLint.Tests/packages.lock.json",
            }, closure.ExactPaths);
            Assert.Equal(new[] {
                "tools/StrataLint.Engine", "tools/StrataLint.EngineeringScope",
                "tools/Trureturing.Truth", "tools/tests/StrataLint.ScriptTests",
                "tools/tests/StrataLint.Tests",
            }, closure.DirectoryPrefixes);
        }
    }

    [Fact]
    public void CrossTreeSyntacticRootInitializerMatchesSameTreeVerdict()
    {
        // Base's same-tree syntax branch recognises Root.FullPath, but ResolvePath
        // cannot resolve that provider, so AddResolved fails closed with this message.
        foreach (var crossTree in new[] { false, true })
        {
            var error = Assert.Throws<InvalidDataException>(() =>
                Derive(RootInitializerSnapshot("holder.Root.FullPath", crossTree), []));
            Assert.Equal("ScriptTests gate Cases.Root: unresolved repository-rooted path expression", error.Message);
        }
    }

    private static RepositorySnapshot RootInitializerSnapshot(string initializer, bool crossTree)
    {
        const string test = """
            using Xunit;
            partial class Cases {
              [Fact] public void Root() => _ = System.IO.File.ReadAllText(CrossTreeRoot);
            }
            """;
        var fields = $$"""
            partial class Cases {
              static readonly Holder holder = new();
              static readonly string CrossTreeRoot = {{initializer}};
            }
            readonly record struct RepositoryRoot(string FullPath);
            sealed class Holder { public RepositoryRoot Root { get; } = new(""); }
            """;
        var snapshot = WithFiles(CurrentSnapshot(), (ScriptTestsSource, test + (crossTree ? "" : fields)));
        return crossTree
            ? WithFiles(snapshot, ("tools/tests/StrataLint.ScriptTests/B.cs", fields))
            : snapshot;
    }
}
