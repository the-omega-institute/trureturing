using System.Security.Cryptography;
using System.Text;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeSourceCommandTests
{
    [Fact]
    public void VerifySourceDoesNotEvaluateDefinitionsAssembly()
    {
        using var root = Prepare();
        Write(root, "file", []);
        Manifest(root, Entry("file", []));
        var output = new StringWriter();
        var error = new StringWriter();

        var code = ScribeCli.Run(
            () => throw new InvalidOperationException("Definitions assembly must not be evaluated."),
            Arguments(root), root.Path, output, error);

        Assert.Equal(0, code);
        Assert.Equal("resources verify-source: entries=1" + Environment.NewLine, output.ToString());
        Assert.Empty(error.ToString());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EqualTreeIncludingEmptyBlobAndUnusualPathsSucceeds(bool sha256)
    {
        using var root = Prepare();
        Write(root, "empty", []);
        Write(root, "nested/sp ace\tline\nfile", [0, 255, 10]);
        var empty = ObjectId([], sha256);
        if (!sha256) Assert.Equal("e69de29bb2d1d6434b8b29ae775ad8c2e48c5391", empty);
        Manifest(root, Entry("empty", [], sha256: sha256)
            + Entry("nested/sp ace\tline\nfile", [0, 255, 10], sha256: sha256), sha256);
        var (code, output, error) = Run(root);
        Assert.Equal(0, code);
        Assert.Equal("resources verify-source: entries=2" + Environment.NewLine, output);
        Assert.Empty(error);
    }

    [Theory]
    [InlineData("different", "SourceContentMismatch")]
    [InlineData("missing", "MissingSourceEntry")]
    [InlineData("directory", "SourceTypeMismatch")]
    [InlineData("crlf", "SourceContentMismatch")]
    public void DiskMismatchIsRejected(string change, string reason)
    {
        using var root = Prepare();
        var bytes = Encoding.UTF8.GetBytes("neutral\n");
        Manifest(root, Entry("file", bytes));
        switch (change)
        {
            case "different": Write(root, "file", Encoding.UTF8.GetBytes("other\n")); break;
            case "directory": TemporaryFileSystem.Directory.CreateDirectory(root.Resolve("file")); break;
            case "crlf": Write(root, "file", Encoding.UTF8.GetBytes("neutral\r\n")); break;
        }
        var (code, _, error) = Run(root);
        Assert.Equal(1, code);
        Assert.Contains(reason + ": file", error, StringComparison.Ordinal);
    }

    [Fact]
    public void AllMismatchesAreCountedAndReported()
    {
        using var root = Prepare();
        Manifest(root, Entry("first", []) + Entry("second", []));
        var (code, _, error) = Run(root);
        Assert.Equal(1, code);
        Assert.Contains("MissingSourceEntry: first", error, StringComparison.Ordinal);
        Assert.Contains("MissingSourceEntry: second", error, StringComparison.Ordinal);
        Assert.Contains("mismatches=2", error, StringComparison.Ordinal);
    }

    [Fact]
    public void ReleaseInputClosureReportsEveryAdditionalFileAndIgnoresOutsideFiles()
    {
        using var root = Prepare();
        Write(root, "Blueprint/ordinary", [1]);
        Write(root, "Blueprint/.hidden", [2]);
        Write(root, "Blueprint/ignored.ignored", [3]);
        Write(root, ".gitignore", Encoding.UTF8.GetBytes("*.ignored\n"));
        TemporaryFileSystem.Directory.CreateDirectory(root.Resolve("Blueprint/nested"));
        Write(root, "Blueprint/nested/deep", [4]);
        TemporaryFileSystem.Directory.CreateDirectory(root.Resolve("Golden/Projection"));
        Write(root, "Golden/Projection/projection.json", [5]);
        Write(root, "outside", [6]);
        Manifest(root, "");
        var (code, _, error) = Run(root);
        Assert.True(code == 1, error.ToString());
        foreach (var path in new[]
        {
            "Blueprint/ordinary", "Blueprint/.hidden", "Blueprint/ignored.ignored",
            "Blueprint/nested/deep", "Golden/Projection/projection.json",
        })
        {
            Assert.Contains("UnexpectedSourceInput: " + path, error, StringComparison.Ordinal);
        }
        Assert.DoesNotContain("outside", error, StringComparison.Ordinal);
    }

    [Fact]
    public void EveryContentMismatchBeyondTwentyIsNamed()
    {
        using var root = Prepare();
        var paths = Enumerable.Range(0, 25).Select(index => $"entry-{index:00}").ToArray();
        Manifest(root, string.Concat(paths.Select(path => Entry(path, []))));
        var (code, _, error) = Run(root);
        Assert.Equal(1, code);
        foreach (var path in paths)
            Assert.Contains("MissingSourceEntry: " + path, error, StringComparison.Ordinal);
        Assert.Equal(25, error.Split(Environment.NewLine, StringSplitOptions.RemoveEmptyEntries)
            .Count(line => line.StartsWith("MissingSourceEntry:", StringComparison.Ordinal)));
    }

    [Fact]
    public void ReleaseInputClosureTreatsASymbolicLinkAsOneFile()
    {
        if (OperatingSystem.IsWindows()) return;
        using var root = Prepare();
        File.CreateSymbolicLink(root.Resolve("Blueprint/link"), "missing-target");
        Manifest(root, "");
        var (code, _, error) = Run(root);
        Assert.Equal(1, code);
        Assert.Contains("UnexpectedSourceInput: Blueprint/link", error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SymbolicLinkUsesTargetStringIncludingDanglingTarget(bool mismatch)
    {
        if (OperatingSystem.IsWindows()) return;
        using var root = Prepare();
        Write(root, "target", Encoding.UTF8.GetBytes("file contents"));
        File.CreateSymbolicLink(root.Resolve("link"), mismatch ? "target" : "absent");
        Manifest(root, Entry("link", Encoding.UTF8.GetBytes("absent"), "120000"));
        var (code, _, error) = Run(root);
        Assert.Equal(mismatch ? 1 : 0, code);
        if (mismatch) Assert.Contains("SourceContentMismatch: link", error, StringComparison.Ordinal);
        else Assert.Empty(error);
    }

    [Fact]
    public void EqualLinkTargetIsHashedInsteadOfReferentContents()
    {
        if (OperatingSystem.IsWindows()) return;
        using var root = Prepare();
        Write(root, "target", Encoding.UTF8.GetBytes("different from target name"));
        File.CreateSymbolicLink(root.Resolve("link"), "target");
        Manifest(root, Entry("link", Encoding.UTF8.GetBytes("target"), "120000"));
        Assert.Equal(0, Run(root).Code);
    }

    [Theory]
    [InlineData("100644")]
    [InlineData("120000")]
    public void FileAndLinkTypesMustMatch(string mode)
    {
        if (OperatingSystem.IsWindows()) return;
        using var root = Prepare();
        Write(root, "target", []);
        if (mode == "100644") File.CreateSymbolicLink(root.Resolve("file"), "target");
        else Write(root, "file", Encoding.UTF8.GetBytes("target"));
        Manifest(root, Entry("file", Encoding.UTF8.GetBytes("target"), mode));
        var (code, _, error) = Run(root);
        Assert.Equal(1, code);
        Assert.Contains("SourceTypeMismatch: file", error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("100644", true)]
    [InlineData("100755", false)]
    public void PermissionBitsDoNotChangeContentEquality(string mode, bool executable)
    {
        if (OperatingSystem.IsWindows()) return;
        using var root = Prepare();
        Write(root, "file", []);
        File.SetUnixFileMode(root.Resolve("file"), UnixFileMode.UserRead | UnixFileMode.UserWrite
            | (executable ? UnixFileMode.UserExecute : UnixFileMode.None));
        Manifest(root, Entry("file", [], mode));
        Assert.Equal(0, Run(root).Code);
    }

    [Theory]
    [InlineData("missing-fields")]
    [InlineData("short-oid")]
    [InlineData("nonhex-oid")]
    [InlineData("newline-separated")]
    [InlineData("duplicate")]
    [InlineData("escape")]
    [InlineData("absolute")]
    [InlineData("windows-absolute")]
    [InlineData("backslash")]
    [InlineData("empty-component")]
    [InlineData("dot-component")]
    [InlineData("invalid-utf8")]
    public void MalformedTreeReturnsExitTwo(string shape)
    {
        using var root = Prepare();
        var entry = Entry("file", []);
        var text = shape switch
        {
            "missing-fields" => "100644\tfile\0",
            "short-oid" => "100644 blob abcd\tfile\0",
            "nonhex-oid" => "100644 blob " + new string('g', 40) + "\tfile\0",
            "newline-separated" => entry.Replace('\0', '\n'),
            "duplicate" => entry + entry,
            "escape" => Entry("../file", []),
            "absolute" => Entry("/file", []),
            "windows-absolute" => Entry("C:/file", []),
            "backslash" => Entry("nested\\file", []),
            "empty-component" => Entry("nested//file", []),
            "dot-component" => Entry("nested/./file", []),
            _ => entry,
        };
        Write(root, "tree", Encoding.UTF8.GetBytes(text));
        if (shape == "invalid-utf8") Write(root, "tree", [255, 0]);
        var (code, _, error) = Run(root);
        Assert.Equal(2, code);
        Assert.Contains("InvalidSourceTree:", error, StringComparison.Ordinal);
    }

    [Fact]
    public void UnreadableTreeReturnsExitTwo()
    {
        using var root = Prepare();
        var (code, _, error) = Run(root);
        Assert.Equal(2, code);
        Assert.Contains("SourceTreeReadFailed:", error, StringComparison.Ordinal);
    }

    [Fact]
    public void SubmoduleIsNamedAndRejected()
    {
        using var root = Prepare();
        Manifest(root, "160000 commit " + new string('a', 40) + "\tmodule\0");
        var (code, _, error) = Run(root);
        Assert.Equal(1, code);
        Assert.Contains("UnsupportedSourceEntry: module (160000 commit)", error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("resources", "verify-source")]
    [InlineData("resources", "verify-source", "--other", "tree")]
    public void InvalidArgumentsReturnExitTwo(params string[] arguments)
    {
        using var root = Prepare();
        var error = new StringWriter();
        Assert.Equal(2, ScribeCli.Run(typeof(ScribeResourcePack).Assembly, arguments,
            root.Path, TextWriter.Null, error));
        Assert.Contains("resources verify-source --source-commit", error.ToString(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EmptyTreeMatchesKnownObjectId(bool sha256)
    {
        using var root = Prepare();
        var treeId = ExpectedTreeId("", sha256);
        if (!sha256) Assert.Equal("4b825dc642cb6eb9a060e54bf8d69288fbee4904", treeId);
        Manifest(root, "", sha256);
        Assert.Equal(0, Run(root).Code);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ChangedCommitByteIsNamedAndRejected(bool sha256)
    {
        using var root = Prepare();
        Manifest(root, "", sha256);
        var originalId = Arguments(root)[3];
        var bytes = TemporaryFileSystem.File.ReadAllBytes(root.Resolve("commit"));
        bytes[^2] ^= 1;
        Write(root, "commit", bytes);
        var (code, _, error) = Run(root, originalId);
        Assert.Equal(1, code);
        Assert.Contains("SourceCommitMismatch:", error, StringComparison.Ordinal);
    }

    [Fact]
    public void UnrelatedSourceCommitIsNamedAndRejected()
    {
        using var root = Prepare();
        Manifest(root, "");
        var (code, _, error) = Run(root, new string('a', 40));
        Assert.Equal(1, code);
        Assert.Contains("SourceCommitMismatch:", error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("parent aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n")]
    [InlineData("tree not-an-object-id\n")]
    [InlineData("tree aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")]
    public void MalformedCommitFirstLineReturnsExitTwo(string firstLine)
    {
        using var root = Prepare();
        Write(root, "commit", Encoding.UTF8.GetBytes(firstLine));
        Write(root, "tree", []);
        var (code, _, error) = Run(root);
        Assert.Equal(2, code);
        Assert.Contains("InvalidSourceCommit:", error, StringComparison.Ordinal);
    }

    [Fact]
    public void UnreadableCommitReturnsExitTwo()
    {
        using var root = Prepare();
        var arguments = Arguments(root);
        TemporaryFileSystem.File.Delete(root.Resolve("commit"));
        var error = new StringWriter();
        Assert.Equal(2, ScribeCli.Run(typeof(ScribeResourcePack).Assembly, arguments,
            root.Path, TextWriter.Null, error));
        Assert.Contains("SourceCommitReadFailed:", error.ToString(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("missing", false)]
    [InlineData("extra", false)]
    [InlineData("object-id", false)]
    [InlineData("missing", true)]
    [InlineData("extra", true)]
    [InlineData("object-id", true)]
    public void ChangedTreeIsRejectedEvenWhenDiskMatchesManifest(string change, bool sha256)
    {
        using var root = Prepare();
        Write(root, "first", []);
        Write(root, "second", []);
        var first = Entry("first", [], sha256: sha256);
        var second = Entry("second", [], sha256: sha256);
        Manifest(root, first + second, sha256);
        var changed = change switch
        {
            "missing" => first,
            "extra" => first + second + Entry("third", [], sha256: sha256),
            _ => first + Entry("second", [1], sha256: sha256),
        };
        if (change == "extra") Write(root, "third", []);
        if (change == "object-id") Write(root, "second", [1]);
        Write(root, "tree", Encoding.UTF8.GetBytes(changed));
        var (code, _, error) = Run(root);
        Assert.Equal(1, code);
        Assert.Contains("SourceRootTreeMismatch:", error, StringComparison.Ordinal);
        Assert.DoesNotContain("SourceContentMismatch:", error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DirectorySortUsesSlashAndRawUtf8Bytes(bool sha256)
    {
        using var root = Prepare();
        var paths = new[] { "a.b", "a/leaf", "a-b", "a0", "é", "z" };
        foreach (var path in paths) Write(root, path, []);
        Manifest(root, string.Concat(paths.Select(path => Entry(path, [], sha256: sha256))), sha256);
        Assert.Equal(0, Run(root).Code);
    }

    [Theory]
    [InlineData("100644", "tree")]
    [InlineData("100755", "commit")]
    [InlineData("120000", "tree")]
    [InlineData("040000", "blob")]
    [InlineData("40000", "tree")]
    [InlineData("160000", "commit")]
    public void EntryTypeAndModeMustBeSupportedTogether(string mode, string type)
    {
        using var root = Prepare();
        Write(root, "file", []);
        Manifest(root, $"{mode} {type} {ObjectId([], false)}\tfile\0");
        var (code, _, error) = Run(root);
        Assert.Equal(1, code);
        Assert.Contains($"UnsupportedSourceEntry: file ({mode} {type})", error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("a", "a/leaf")]
    [InlineData("a/leaf", "a")]
    public void FileDirectoryCollisionReturnsExitTwo(string first, string second)
    {
        using var root = Prepare();
        Write(root, "tree", Encoding.UTF8.GetBytes(Entry(first, []) + Entry(second, [])));
        var (code, _, error) = Run(root);
        Assert.Equal(2, code);
        Assert.Contains("InvalidSourceTree:", error, StringComparison.Ordinal);
    }

    [Fact]
    public void MissingCommitFromCannotPass()
    {
        using var root = Prepare();
        Manifest(root, "");
        var arguments = Arguments(root).Where((_, index) => index is not (4 or 5)).ToArray();
        var error = new StringWriter();
        Assert.Equal(2, ScribeCli.Run(typeof(ScribeResourcePack).Assembly, arguments,
            root.Path, TextWriter.Null, error));
        Assert.Contains("--commit-from", error.ToString(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false, "c4d245dbea9d7756087c2a4864495cadd8ec22dd")]
    [InlineData(true, "ae31fd44157872b9cab43436b3262ae34fbd1dfd3afccb2a92a63555938a093f")]
    public void LargeFileMatchesKnownObjectIdAcrossReadBuffers(bool sha256, string expected)
    {
        using var root = Prepare();
        var bytes = Enumerable.Range(0, 1048593).Select(index => (byte)(index % 251)).ToArray();
        Write(root, "large", bytes);
        Assert.Equal(expected, ObjectId(bytes, sha256));
        Manifest(root, $"100644 blob {expected}\tlarge\0", sha256);
        Assert.Equal(0, Run(root).Code);
    }

    private static TemporaryRoot Prepare()
    {
        var root = new TemporaryRoot();
        Write(root, "global.json", Encoding.UTF8.GetBytes("{}"));
        TemporaryFileSystem.Directory.CreateDirectory(root.Resolve("Blueprint"));
        Commit(root, "4b825dc642cb6eb9a060e54bf8d69288fbee4904");
        return root;
    }

    private static void Write(TemporaryRoot root, string path, byte[] bytes) =>
        TemporaryFileSystem.File.WriteAllBytes(root.Resolve(path), bytes);

    private static void Manifest(TemporaryRoot root, string text, bool sha256 = false)
    {
        Write(root, "tree", Encoding.UTF8.GetBytes(text));
        Commit(root, ExpectedTreeId(text, sha256));
    }

    private static void Commit(TemporaryRoot root, string treeId) => Write(root, "commit",
        Encoding.UTF8.GetBytes($"tree {treeId}\nauthor Neutral <neutral@example.invalid> 0 +0000\n"
            + "committer Neutral <neutral@example.invalid> 0 +0000\n\nNeutral fixture\n"));

    private static string ExpectedTreeId(string manifest, bool sha256)
    {
        var records = manifest.Split('\0', StringSplitOptions.RemoveEmptyEntries).Select(record =>
        {
            var tab = record.IndexOf('\t');
            var metadata = record[..tab].Split(' ');
            return (Path: record[(tab + 1)..], Mode: metadata[0], Id: metadata[2]);
        }).ToArray();
        return EncodeDirectory(records);

        string EncodeDirectory(IEnumerable<(string Path, string Mode, string Id)> leaves)
        {
            var entries = leaves.GroupBy(leaf => leaf.Path.Split('/')[0], StringComparer.Ordinal).Select(group =>
            {
                var directory = group.First().Path.Contains('/');
                return (Name: group.Key, Mode: directory ? "40000" : group.Single().Mode,
                    Id: directory ? EncodeDirectory(group.Select(leaf =>
                        (leaf.Path[(group.Key.Length + 1)..], leaf.Mode, leaf.Id))) : group.Single().Id,
                    Sort: Convert.ToHexString(Encoding.UTF8.GetBytes(group.Key + (directory ? "/" : ""))));
            });
            var body = entries.OrderBy(entry => entry.Sort, StringComparer.Ordinal).SelectMany(entry =>
                Encoding.UTF8.GetBytes($"{entry.Mode} {entry.Name}\0").Concat(Convert.FromHexString(entry.Id))).ToArray();
            return ObjectId(body, sha256, "tree");
        }
    }

    private static string Entry(string path, byte[] bytes, string mode = "100644", bool sha256 = false) =>
        $"{mode} blob {ObjectId(bytes, sha256)}\t{path}\0";

    private static string ObjectId(byte[] bytes, bool sha256, string kind = "blob")
    {
        var input = Encoding.UTF8.GetBytes(FormattableString.Invariant($"{kind} {bytes.Length}\0"))
            .Concat(bytes).ToArray();
        return Convert.ToHexStringLower(sha256 ? SHA256.HashData(input) : SHA1.HashData(input));
    }

    private static string[] Arguments(TemporaryRoot root, string? sourceCommit = null)
    {
        var bytes = TemporaryFileSystem.File.ReadAllBytes(root.Resolve("commit"));
        var sha256 = Encoding.UTF8.GetString(bytes).Split('\n')[0].Length == 69;
        return ["resources", "verify-source", "--source-commit", sourceCommit ?? ObjectId(bytes, sha256, "commit"),
            "--commit-from", "commit", "--tree-from", "tree"];
    }

    private static (int Code, string Output, string Error) Run(TemporaryRoot root, string? sourceCommit = null)
    {
        var output = new StringWriter();
        var error = new StringWriter();
        var code = ScribeCli.Run(typeof(ScribeResourcePack).Assembly,
            Arguments(root, sourceCommit), root.Path, output, error);
        return (code, output.ToString(), error.ToString());
    }
}
