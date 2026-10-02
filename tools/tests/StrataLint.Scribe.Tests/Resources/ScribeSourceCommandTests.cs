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
            ["resources", "verify-source", "--tree-from", "tree"], root.Path, output, error);

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
            + Entry("nested/sp ace\tline\nfile", [0, 255, 10], sha256: sha256));
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
        Manifest(root, text);
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
        Assert.Contains("resources verify-source --tree-from", error.ToString(), StringComparison.Ordinal);
    }

    private static TemporaryRoot Prepare()
    {
        var root = new TemporaryRoot();
        Write(root, "global.json", Encoding.UTF8.GetBytes("{}"));
        TemporaryFileSystem.Directory.CreateDirectory(root.Resolve("Blueprint"));
        return root;
    }

    private static void Write(TemporaryRoot root, string path, byte[] bytes) =>
        TemporaryFileSystem.File.WriteAllBytes(root.Resolve(path), bytes);

    private static void Manifest(TemporaryRoot root, string text) => Write(root, "tree", Encoding.UTF8.GetBytes(text));

    private static string Entry(string path, byte[] bytes, string mode = "100644", bool sha256 = false) =>
        $"{mode} blob {ObjectId(bytes, sha256)}\t{path}\0";

    private static string ObjectId(byte[] bytes, bool sha256)
    {
        var input = Encoding.UTF8.GetBytes(FormattableString.Invariant($"blob {bytes.Length}\0"))
            .Concat(bytes).ToArray();
        return Convert.ToHexStringLower(sha256 ? SHA256.HashData(input) : SHA1.HashData(input));
    }

    private static (int Code, string Output, string Error) Run(TemporaryRoot root)
    {
        var output = new StringWriter();
        var error = new StringWriter();
        var code = ScribeCli.Run(typeof(ScribeResourcePack).Assembly,
            ["resources", "verify-source", "--tree-from", "tree"], root.Path, output, error);
        return (code, output.ToString(), error.ToString());
    }
}
