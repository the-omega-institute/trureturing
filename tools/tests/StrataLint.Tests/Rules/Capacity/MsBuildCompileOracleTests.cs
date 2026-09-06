using System.Text;
using StrataLint.Engine;
using Directory = StrataLint.TestSupport.TemporaryFileSystem.Directory;
using File = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

public sealed class MsBuildCompileOracleTests
{
    [Fact]
    public void MaterializeWritesExactlyTheDerivationInputProjection()
    {
        var snapshot = ProjectionSnapshot();
        using var checkout = MsBuildCompileOracle.Materialize(snapshot, ScribeTestMapDeriver.IsDerivationInput);

        Assert.Equal(ExpectedPaths(), RelativeFiles(checkout.Root));
        foreach (var path in ExpectedPaths())
        {
            Assert.True(snapshot.TryGetFile(path, out var file));
            Assert.Equal(file.RawBytes.ToArray(), File.ReadAllBytes(Path.Combine(checkout.Root, path)));
        }
    }

    [Fact]
    public void MaterializeKeepsNestedLayoutAndRawBytes()
    {
        const string Source = "\uFEFF// raw bytes \t\r\nclass Deep {}\r\n \t";
        var snapshot = Snapshot(("src/deep/nested/Deep.cs", Source));
        string checkoutRoot;
        using (var checkout = MsBuildCompileOracle.Materialize(snapshot, ScribeTestMapDeriver.IsDerivationInput))
        {
            checkoutRoot = checkout.Root;
            Assert.Equal(["src/deep/nested/Deep.cs"], RelativeFiles(checkout.Root));
            Assert.Equal(Encoding.UTF8.GetBytes(Source),
                File.ReadAllBytes(Path.Combine(checkout.Root, "src", "deep", "nested", "Deep.cs")));
        }

        Assert.False(Directory.Exists(checkoutRoot));
    }

    [Fact]
    public void DeriveSnapshotOnlyMaterializesDerivationInputs()
    {
        var snapshot = ProjectionSnapshot();
        var calls = 0;
        string? checkoutRoot = null;
        var map = ScribeTestMapDeriver.DeriveSnapshot(snapshot, _ => [], input =>
            ScribeTestMapDeriver.DeriveSnapshotUncached(input,
                (host, arguments, repositoryRoot, timeout, maximumOutputBytes, standardInput, environment) =>
                {
                    calls++;
                    checkoutRoot = repositoryRoot;
                    Assert.Equal(ExpectedPaths(), RelativeFiles(repositoryRoot));
                    Assert.Equal("p/p.csproj", arguments.ElementAt(1));
                    Assert.Contains("-getItem:Compile", arguments);
                    Assert.Contains("-property:ImportDirectoryBuildProps=true", arguments);
                    Assert.Contains("-property:DirectoryBuildPropsPath="
                        + Path.Combine(repositoryRoot, "Directory.Build.props"), arguments);
                    return new ProcessOutput(0, "{\"Items\":{\"Compile\":[]}}"u8.ToArray(), []);
                }));

        Assert.Equal(1, calls);
        Assert.Empty(map.CompileQueryFindings);
        Assert.NotNull(checkoutRoot);
        Assert.False(Directory.Exists(checkoutRoot));
    }

    [Fact]
    public void DeriveSnapshotMaterializationFailureProducesProjectFindings()
    {
        // Both entries are in the projection; either enumeration order causes a file/directory conflict.
        var snapshot = Snapshot(
            ("conflict.cs", "// file"),
            ("conflict.cs/child.cs", "// child"),
            ("p/one.csproj", "<Project />"),
            ("q/two.csproj", "<Project />"));
        var calls = 0;
        var map = ScribeTestMapDeriver.DeriveSnapshot(snapshot, _ => [], input =>
            ScribeTestMapDeriver.DeriveSnapshotUncached(input,
                (host, arguments, repositoryRoot, timeout, maximumOutputBytes, standardInput, environment) =>
                {
                    calls++;
                    return new ProcessOutput(0, "{\"Items\":{\"Compile\":[]}}"u8.ToArray(), []);
                }));

        Assert.Equal(0, calls);
        Assert.Equal(["p/one.csproj", "q/two.csproj"],
            map.CompileQueryFindings.Select(static finding => finding.Path).Order(StringComparer.Ordinal));
        Assert.All(map.CompileQueryFindings, static finding =>
            Assert.StartsWith("MSBuild snapshot materialization failed closed:", finding.Message));
    }

    private static string[] ExpectedPaths() =>
    [
        "Directory.Build.props",
        "Directory.Packages.props",
        "NuGet.Config",
        "a.cs",
        "global.json",
        "p/p.csproj",
        "p/packages.lock.json",
        "tools/x.targets",
    ];

    private static string[] RelativeFiles(string root) => Directory
        .EnumerateFiles(root, "*", SearchOption.AllDirectories)
        .Select(path => Path.GetRelativePath(root, path).Replace(Path.DirectorySeparatorChar, '/'))
        .Order(StringComparer.Ordinal)
        .ToArray();

    private static RepositorySnapshot ProjectionSnapshot() => Snapshot(
        ("a.cs", "class A {}"),
        ("p/p.csproj", "<Project />"),
        ("Directory.Build.props", "<Project />"),
        ("tools/x.targets", "<Project />"),
        ("global.json", "{}"),
        ("NuGet.Config", "<configuration />"),
        ("p/packages.lock.json", "{\"dependencies\":{\"net10.0\":{}}}"),
        ("Directory.Packages.props", "<Project />"),
        ("README.md", "readme"),
        ("D5/x.lean", "-- Lean fixture"),
        ("Meta/y.yaml", "key: value"),
        ("Golden/z.json", "{}"),
        ("notes.txt", "notes"),
        ("Blueprint/b.md", "blueprint"));

    private static RepositorySnapshot Snapshot(params (string Path, string Text)[] files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(files.Select(static file =>
                RawRepositoryEntry.FromText(file.Path, file.Text))))).Snapshot;
}
