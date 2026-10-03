using System.Collections.Immutable;
using System.Security.Cryptography;
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeResourceCorrespondenceTests
{
    private const string Shared = "Blueprint/D5/S0/Test/Shared.scribe.cs";
    private const string Data = "Golden/read.json";
    private const string Absent = "Golden/optional.json";

    [Theory]
    [InlineData("entry", 2, 1, 0, 0)]
    [InlineData("shared", 0, 3, 0, 0)]
    [InlineData("data", 1, 2, 0, 0)]
    [InlineData("create-missing", 1, 2, 0, 0)]
    [InlineData("new-definition", 3, 0, 0, 1)]
    [InlineData("delete-definition", 2, 0, 1, 0)]
    public void ChangesHaveStructuredCategoriesAndFirstInput(
        string change, int consistent, int changed, int packOnly, int diskOnly)
    {
        using var root = Prepare();
        var pack = Pack(root);
        var inputPath = change switch
        {
            "shared" => Shared,
            "data" => Data,
            "create-missing" => Absent,
            "new-definition" => PathFor("Gamma"),
            _ => PathFor("Alpha"),
        };
        var recorded = File.Exists(root.Resolve(inputPath)) ? Digest(root, inputPath) : null;
        if (change == "delete-definition") TemporaryFileSystem.File.Delete(root.Resolve(inputPath));
        else TemporaryFileSystem.File.AppendAllText(root.Resolve(inputPath), "\n");
        var actual = File.Exists(root.Resolve(inputPath)) ? Digest(root, inputPath) : null;

        var result = ScribeResourceCorrespondence.Compare(pack, root.Path);

        Assert.False(result.IsCorresponding);
        Assert.Equal(consistent, result.ConsistentCount);
        Assert.Equal(changed, result.InputsChanged.Length);
        Assert.Equal(packOnly, result.PackOnly.Length);
        Assert.Equal(diskOnly, result.DiskOnly.Length);
        var differences = result.InputsChanged.Concat(result.PackOnly).Concat(result.DiskOnly).ToArray();
        Assert.All(differences, difference =>
        {
            Assert.Equal(inputPath, difference.InputPath);
            Assert.Equal(recorded, difference.RecordedSha256);
            Assert.Equal(actual, difference.CurrentSha256);
        });
        Assert.Equal(change == "new-definition" ? PathFor("Gamma") : PathFor("Alpha"),
            differences[0].DefinitionPath);
    }

    [Fact]
    public void ComparisonScansAllDefinitionsAndKeepsOnlyTheFirstDifferencePerDefinition()
    {
        using var root = Prepare();
        var pack = Pack(root);
        TemporaryFileSystem.File.AppendAllText(root.Resolve(PathFor("Alpha")), "\n");
        TemporaryFileSystem.File.AppendAllText(root.Resolve(Data), "\n");

        var result = ScribeResourceCorrespondence.Compare(pack, root.Path);

        Assert.Equal(1, result.ConsistentCount);
        Assert.Collection(result.InputsChanged,
            alpha =>
            {
                Assert.Equal(PathFor("Alpha"), alpha.DefinitionPath);
                Assert.Equal(PathFor("Alpha"), alpha.InputPath);
            },
            beta =>
            {
                Assert.Equal(PathFor("Beta"), beta.DefinitionPath);
                Assert.Equal(Data, beta.InputPath);
            });
        Assert.Empty(result.PackOnly);
        Assert.Empty(result.DiskOnly);
    }

    [Fact]
    public void SameTreeIsCorrespondingIncludingRecordedMissingInputs()
    {
        using var root = Prepare();
        var pack = Pack(root);
        TemporaryFileSystem.File.WriteAllText(root.Resolve("Golden/unread.json"), "unread");

        var result = ScribeResourceCorrespondence.Compare(pack, root.Path);

        Assert.True(result.IsCorresponding);
        Assert.Equal(3, result.ConsistentCount);
        Assert.Empty(result.InputsChanged);
        Assert.Empty(result.PackOnly);
        Assert.Empty(result.DiskOnly);
    }

    [Fact]
    public void SnapshotComparisonPreservesCapturedInputsAndDefinitionInventory()
    {
        using var root = Prepare();
        var raw = RawRepositorySnapshot.Create(Directory.GetFiles(root.Path, "*", SearchOption.AllDirectories)
            .Select(path => new RawRepositoryEntry(Path.GetRelativePath(root.Path, path).Replace('\\', '/'),
                ImmutableArray.CreateRange(File.ReadAllBytes(path)))));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var pack = Pack(root);
        TemporaryFileSystem.File.AppendAllText(root.Resolve(PathFor("Alpha")), "\n");
        TemporaryFileSystem.File.AppendAllText(root.Resolve(Shared), "\n");
        TemporaryFileSystem.File.AppendAllText(root.Resolve(Data), "\n");
        TemporaryFileSystem.File.Delete(root.Resolve(PathFor("Beta")));
        TemporaryFileSystem.File.WriteAllText(root.Resolve(Absent), "{}");
        TemporaryFileSystem.File.WriteAllText(root.Resolve(PathFor("Gamma")), "// definition fixture\n");

        var result = ScribeResourceCorrespondence.Compare(pack, new SnapshotScribeResourceFileView(snapshot));

        Assert.True(result.IsCorresponding);
        Assert.Equal(3, result.ConsistentCount);
        var workingTree = ScribeResourceCorrespondence.Compare(pack, new WorkingTreeScribeResourceFileView(root.Path));
        Assert.False(workingTree.IsCorresponding);
        Assert.Equal(PathFor("Beta"), Assert.Single(workingTree.PackOnly).DefinitionPath);
        Assert.Equal(PathFor("Gamma"), Assert.Single(workingTree.DiskOnly).DefinitionPath);
    }

    [Fact]
    public void SnapshotViewDistinguishesEmptyFilesFromMissingFiles()
    {
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create([RawRepositoryEntry.FromText(Data, string.Empty)]))).Snapshot;
        var files = new SnapshotScribeResourceFileView(snapshot);

        Assert.Equal(ImmutableArray<byte>.Empty, files.ReadBytes(Data));
        Assert.Null(files.ReadBytes(Absent));
        Assert.Empty(files.EnumerateDefinitionPaths());
    }

    private static TemporaryRoot Prepare()
    {
        var root = new TemporaryRoot();
        foreach (var name in new[] { "Alpha", "Beta", "Shared" })
            TemporaryFileSystem.File.WriteAllText(root.Resolve(PathFor(name)), "// definition fixture\n");
        TemporaryFileSystem.File.WriteAllText(root.Resolve(Data), "{}");
        return root;
    }

    private static ScribeResourcePack Pack(TemporaryRoot root)
    {
        var definitions = new[] { "Alpha", "Beta", "Shared" }.Select(name => DocumentDefinition.Create(
            ScribeDocument.Create(Header("D5/S0/Test/" + name, "Fixture"), H("Fixture"),
                Blocks(Paragraph(Text("Body")))), PathFor(name))).ToArray();
        var inputs = definitions.ToDictionary(definition => definition.Document.Header.Gid.Value, definition =>
        {
            var entry = "Blueprint/" + definition.Document.Header.Gid.Value + ".scribe.cs";
            var paths = entry == Shared ? new[] { entry } : new[] { entry, Shared, Data, Absent };
            return paths.Select(path => new ScribeResourceInput(path,
                File.Exists(root.Resolve(path)) ? Digest(root, path) : null)).ToImmutableArray();
        }, StringComparer.Ordinal);
        var packPath = root.Resolve("resources.zip");
        ScribeResourcePack.Write(packPath, definitions, inputs);
        return ScribeResourcePack.Open(packPath);
    }

    private static string PathFor(string name) => "Blueprint/D5/S0/Test/" + name + ".scribe.cs";
    private static string Digest(TemporaryRoot root, string path) =>
        Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(root.Resolve(path))));
}
