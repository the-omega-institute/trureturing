using System.Text;
using System.Text.Json.Nodes;
using System.Security.Cryptography;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeReleaseCommandTests
{
    [Fact]
    public void ReleaseRejectsFileTargetWithoutTouchingIt()
    {
        using var root = Prepare();
        TemporaryFileSystem.File.WriteAllText(root.Resolve("release"), "content");
        var error = new StringWriter();
        Assert.Equal(2, Release(root, error: error));
        Assert.Contains("InvalidReleaseDirectory", error.ToString(), StringComparison.Ordinal);
        Assert.Equal("content", File.ReadAllText(root.Resolve("release")));
    }

    [Fact]
    public void ReleaseCreatesMissingParentDirectory()
    {
        using var root = Prepare();
        Script(root, "Neutral");
        var error = new StringWriter();
        Assert.False(Directory.Exists(Path.Combine(root.Path, "parent")));
        Assert.Equal(0, Run(root, ["resources", "release", "--out", "parent/release"], error));
        Assert.Empty(error.ToString());
        Assert.Equal(2, Directory.GetFiles(Path.Combine(root.Path, "parent/release")).Length);
    }

    [Fact]
    public void VerifyReleaseRejectsPathsFromOptionWithExitTwo()
    {
        using var root = Assets();
        var error = new StringWriter();
        Assert.Equal(2, Run(root, ["resources", "verify-release", "--dir", "release", "--paths-from", "tree.txt"], error));
        Assert.Contains("InvalidReleaseArguments", error.ToString(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ReleaseHostFailurePreservesTargetDirectory(bool existed)
    {
        using var root = Prepare();
        Script(root, "Alpha", valid: false);
        Script(root, "Beta", valid: false);
        Script(root, "Gamma");
        var target = root.Resolve("release");
        if (existed) TemporaryFileSystem.Directory.CreateDirectory(target);
        var error = new StringWriter();
        Assert.Equal(1, Release(root, error: error));
        var lines = error.ToString().Split(Environment.NewLine, StringSplitOptions.RemoveEmptyEntries);
        Assert.Equal(2, lines.Length);
        Assert.Contains("Alpha.scribe.cs", lines[0], StringComparison.Ordinal);
        Assert.Contains("Beta.scribe.cs", lines[1], StringComparison.Ordinal);
        Assert.All(lines, line => Assert.StartsWith("DefinitionMissing:", line, StringComparison.Ordinal));
        Assert.Equal(existed, Directory.Exists(target));
        if (existed) Assert.Empty(Directory.EnumerateFileSystemEntries(target));
    }

    [Fact]
    public void ReleaseRejectsNonEmptyTargetWithoutTouchingIt()
    {
        using var root = Prepare();
        TemporaryFileSystem.Directory.CreateDirectory(root.Resolve("release"));
        var path = root.Resolve("release/existing");
        TemporaryFileSystem.File.WriteAllText(path, "content");
        var error = new StringWriter();
        Assert.Equal(2, Release(root, error: error));
        Assert.Contains("ReleaseDirectoryNotEmpty", error.ToString(), StringComparison.Ordinal);
        Assert.Equal("content", File.ReadAllText(path));
        Assert.Single(Directory.EnumerateFileSystemEntries(root.Resolve("release")));
    }

    [Theory]
    [InlineData("release", "--out")]
    [InlineData("verify-release", "--dir")]
    public void SourceCommitOptionIsUnknown(string command, string directoryOption)
    {
        using var root = Prepare();
        var error = new StringWriter();
        Assert.Equal(2, Run(root, ["resources", command, directoryOption, "release",
            "--source" + "-commit", new string('0', 40)], error));
        Assert.Contains("InvalidReleaseArguments: unknown, empty or duplicate option.",
            error.ToString(), StringComparison.Ordinal);
        Assert.False(Directory.Exists(root.Resolve("release")));
    }

    [Theory]
    [InlineData("resources", "release")]
    [InlineData("resources", "verify-release")]
    [InlineData("resources", "verify-release", "--dir", "")]
    [InlineData("resources", "verify-release", "--dir", "release", "--unknown", "value")]
    [InlineData("resources", "verify-release", "--dir", "release", "--dir", "release")]
    [InlineData("resources", "verify-release", "--dir", "release", "--total-sha256", "bad")]
    public void InvalidArgumentsReturnTwoAndCompleteUsage(params string[] arguments)
    {
        using var root = Prepare();
        var error = new StringWriter();
        Assert.Equal(2, Run(root, arguments, error));
        Assert.Contains("resources release --out", error.ToString(), StringComparison.Ordinal);
        Assert.Contains("resources verify-release --dir", error.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void VerifyRejectsBundlePackBytesMismatch()
    {
        using var root = Assets();
        var other = root.Resolve("other.zip");
        ScribeResourcePack.Write(other, [ScribeResourcePackTests.Definition("Second")]);
        TemporaryFileSystem.File.WriteAllBytes(root.Resolve("release/" + ScribeReleaseSurface.BundleFile),
            ScribeReleaseSurface.Bundle(File.ReadAllBytes(other)));
        var error = new StringWriter();
        Assert.Equal(1, Verify(root, error));
        Assert.Contains("BundlePackBytesMismatch", error.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void VerifyRejectsBundlePackByteMismatchWithEqualManifest()
    {
        using var root = Assets();
        var zipPath = root.Resolve("release/scribe-resources.zip");
        var other = root.Resolve("other.zip");
        var entries = ScribeResourcePackTests.ReadZip(zipPath);
        entries.Reverse();
        ScribeResourcePackTests.RewriteZip(other, entries);
        Assert.Equal(ScribeResourcePack.Open(zipPath).Manifest.TotalSha256,
            ScribeResourcePack.Open(other).Manifest.TotalSha256);
        Assert.False(File.ReadAllBytes(zipPath).AsSpan().SequenceEqual(File.ReadAllBytes(other)));
        TemporaryFileSystem.File.WriteAllBytes(root.Resolve("release/" + ScribeReleaseSurface.BundleFile),
            ScribeReleaseSurface.Bundle(File.ReadAllBytes(other)));
        var error = new StringWriter();
        Assert.Equal(1, Verify(root, error));
        Assert.Contains("BundlePackBytesMismatch", error.ToString(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("identity.json")]
    [InlineData("extra.txt")]
    [InlineData("nested/extra.txt")]
    public void VerifyRejectsAdditionalFiles(string extra)
    {
        using var root = Assets();
        var path = root.Resolve("release/" + extra);
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        TemporaryFileSystem.File.WriteAllText(path, "extra");
        var error = new StringWriter();
        Assert.Equal(1, Verify(root, error));
        Assert.Contains("UnexpectedReleaseEntry", error.ToString(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("scribe-resources.zip")]
    [InlineData("StrataLint.Scribe.ResourceBundle.dll")]
    public void VerifyRejectsMissingFileWithExitTwo(string file)
    {
        using var root = Assets();
        TemporaryFileSystem.File.Delete(root.Resolve("release/" + file));
        var error = new StringWriter();
        Assert.Equal(2, Verify(root, error));
        Assert.Contains("MissingReleaseAsset", error.ToString(), StringComparison.Ordinal);
        Assert.Contains(file, error.ToString(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("scribe-resources.zip")]
    [InlineData("StrataLint.Scribe.ResourceBundle.dll")]
    public void VerifyRejectsMalformedAssetWithExitTwo(string file)
    {
        using var root = Assets();
        TemporaryFileSystem.File.WriteAllBytes(root.Resolve("release/" + file), [0xff]);
        var error = new StringWriter();
        Assert.Equal(2, Verify(root, error));
        Assert.NotEmpty(error.ToString());
    }

    [Theory]
    [InlineData("--total-sha256", "0000000000000000000000000000000000000000000000000000000000000000", "ExpectedTotalSha256Mismatch")]
    public void VerifyReportsExpectedDigestMismatch(string option, string value, string reason)
    {
        using var root = Assets();
        var error = new StringWriter();
        Assert.Equal(1, Run(root, ["resources", "verify-release", "--dir", "release", option, value], error));
        Assert.Contains(reason, error.ToString(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void VerifyStronglyDecodesBothResourcePacks(bool bundleOnly)
    {
        using var root = Assets();
        var zipPath = root.Resolve("release/scribe-resources.zip");
        var entries = ScribeResourcePackTests.ReadZip(zipPath);
        entries[0] = (entries[0].Name, Encoding.UTF8.GetBytes(Encoding.UTF8.GetString(entries[0].Bytes)
            .Replace("\"type\":\"ScribeDocument\"", "\"type\":\"Unknown\"", StringComparison.Ordinal)));
        var index = entries.FindIndex(item => item.Name == "manifest.json");
        var manifest = JsonNode.Parse(entries[index].Bytes)!;
        manifest["entries"]![0]!["sha256"] = Convert.ToHexStringLower(SHA256.HashData(entries[0].Bytes));
        manifest["totalSha256"] = Convert.ToHexStringLower(SHA256.HashData(
            Encoding.UTF8.GetBytes(manifest["entries"]!.ToJsonString())));
        entries[index] = ("manifest.json", Encoding.UTF8.GetBytes(manifest.ToJsonString()));
        var modified = root.Resolve("modified.zip");
        ScribeResourcePackTests.RewriteZip(modified, entries);
        if (!bundleOnly) TemporaryFileSystem.File.WriteAllBytes(zipPath, File.ReadAllBytes(modified));
        TemporaryFileSystem.File.WriteAllBytes(root.Resolve("release/" + ScribeReleaseSurface.BundleFile),
            ScribeReleaseSurface.Bundle(File.ReadAllBytes(modified)));
        var error = new StringWriter();
        Assert.Equal(2, Verify(root, error));
        Assert.Contains("UnknownType", error.ToString(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ReleaseProducesExactlyTwoAssetsAndVerifies(bool existed)
    {
        using var root = Prepare();
        Script(root, "First");
        Script(root, "Second");
        if (existed) TemporaryFileSystem.Directory.CreateDirectory(root.Resolve("release"));
        var output = new StringWriter();
        var error = new StringWriter();
        Assert.Equal(0, Release(root, output, error));
        Assert.Empty(error.ToString());
        Assert.Equal(new[] { ScribeReleaseSurface.BundleFile, "scribe-resources.zip" },
            Directory.GetFiles(root.Resolve("release")).Select(Path.GetFileName).Order(StringComparer.Ordinal));
        var pack = ScribeResourcePack.Open(root.Resolve("release/scribe-resources.zip"));
        Assert.Equal(2, pack.Manifest.EntryCount);
        Assert.Equal(FormattableString.Invariant($"resources release: entries=2 totalSha256={pack.Manifest.TotalSha256}")
            + Environment.NewLine, output.ToString());
        Assert.Equal(0, Run(root, ["resources", "verify-release", "--dir", "release",
            "--total-sha256", pack.Manifest.TotalSha256], error));
        Assert.Empty(error.ToString());
        Assert.Equal(File.ReadAllBytes(root.Resolve("release/scribe-resources.zip")), ScribeReleaseSurface.Unbundle(
            File.ReadAllBytes(root.Resolve("release/" + ScribeReleaseSurface.BundleFile))));
    }

    private static TemporaryRoot Assets()
    {
        var root = Prepare();
        var target = root.Resolve("release");
        TemporaryFileSystem.Directory.CreateDirectory(target);
        var path = root.Resolve("release/scribe-resources.zip");
        ScribeResourcePack.Write(path, [ScribeResourcePackTests.Definition("First"), ScribeResourcePackTests.Definition("Second")]);
        TemporaryFileSystem.File.WriteAllBytes(root.Resolve("release/" + ScribeReleaseSurface.BundleFile),
            ScribeReleaseSurface.Bundle(File.ReadAllBytes(path)));
        return root;
    }

    private static TemporaryRoot Prepare()
    {
        var root = new TemporaryRoot();
        TemporaryFileSystem.File.WriteAllText(root.Resolve("global.json"), "{}");
        TemporaryFileSystem.Directory.CreateDirectory(root.Resolve("Blueprint"));
        return root;
    }

    private static void Script(TemporaryRoot root, string name, bool valid = true)
    {
        var path = root.Resolve("Blueprint/D5/S0/Test/" + name + ".scribe.cs");
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        TemporaryFileSystem.File.WriteAllText(path, valid ? $$"""
            using StrataLint.Scribe;
            using static StrataLint.Scribe.DefinitionDsl;
            internal sealed class {{name}} : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H("title"), Blocks(Paragraph(Text("content")))));
            }
            """ : "internal sealed class " + name + " { }");
    }

    private static int Release(TemporaryRoot root, TextWriter? output = null, TextWriter? error = null) =>
        ScribeCli.Run(typeof(ScribeResourcePack).Assembly, ["resources", "release", "--out", "release"], root.Path, output ?? TextWriter.Null, error ?? TextWriter.Null);

    private static int Verify(TemporaryRoot root, TextWriter error) =>
        Run(root, ["resources", "verify-release", "--dir", "release"], error);

    private static int Run(TemporaryRoot root, string[] args, TextWriter error) =>
        ScribeCli.Run(typeof(ScribeResourcePack).Assembly, args, root.Path, TextWriter.Null, error);

}
