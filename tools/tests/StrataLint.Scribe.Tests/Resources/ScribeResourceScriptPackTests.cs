using System.Globalization;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeResourceScriptPackTests
{
    [Fact]
    public void PackReportsEveryHostFailureWithoutCreatingOutput()
    {
        using var root = Prepare();
        Write(root.Path, "Alpha", "internal sealed class Alpha { }");
        Write(root.Path, "Beta", "internal sealed class Beta { }");
        Definition(root.Path, "Gamma");
        var error = new StringWriter();
        Assert.Equal(1, Cli(root.Path, ["resources", "pack", "--out", "resources.zip"], TextWriter.Null, error));
        AssertHostFailures(error);
        Assert.False(File.Exists(root.Resolve("resources.zip")));
    }

    [Fact]
    public void PackPreservesAnExistingOutputOnHostFailure()
    {
        using var root = Prepare();
        Write(root.Path, "Alpha", "internal sealed class Alpha { }");
        Write(root.Path, "Beta", "internal sealed class Beta { }");
        Definition(root.Path, "Gamma");
        var path = root.Resolve(PathFor("Gamma"));
        var bytes = File.ReadAllBytes(path);
        var error = new StringWriter();

        Assert.Equal(1, Cli(root.Path, ["resources", "pack", "--out", PathFor("Gamma")], TextWriter.Null, error));
        AssertHostFailures(error);
        Assert.True(File.Exists(path));
        Assert.Equal(bytes, File.ReadAllBytes(path));
    }

    [Fact]
    public void PackPreservesAnExistingOutputDirectoryOnHostFailure()
    {
        using var root = Prepare();
        Write(root.Path, "Alpha", "internal sealed class Alpha { }");
        Write(root.Path, "Beta", "internal sealed class Beta { }");
        Definition(root.Path, "Gamma");
        var path = root.Resolve("resources.zip");
        TemporaryFileSystem.Directory.CreateDirectory(path);
        var error = new StringWriter();

        Assert.Equal(1, Cli(root.Path, ["resources", "pack", "--out", "resources.zip"], TextWriter.Null, error));
        AssertHostFailures(error);
        Assert.True(Directory.Exists(path));
    }

    [Fact]
    public void PackUsesScriptsAndMatchesDirectCanonicalEncoding()
    {
        using var root = Prepare();
        Definition(root.Path, "Alpha");
        Definition(root.Path, "Beta");
        var output = new StringWriter();
        var error = new StringWriter();
        Assert.Equal(0, Cli(root.Path, ["resources", "pack", "--out", "resources.zip"], output, error));
        Assert.Empty(error.ToString());
        var pack = ScribeResourcePack.Open(root.Resolve("resources.zip"));
        Assert.Equal(2, pack.Manifest.EntryCount);
        Assert.Equal(FormattableString.Invariant(
            $"resources pack: entries=2 uncompressedBytes={pack.TotalUncompressedBytes} totalSha256={pack.Manifest.TotalSha256}")
            + Environment.NewLine, output.ToString());
        foreach (var name in new[] { "Alpha", "Beta" })
        {
            var result = ScribeScriptHost.Execute(root.Path, PathFor(name));
            Assert.True(result.IsSuccess, result.Failure?.ToString());
            Assert.Equal(ScribeResourceCodec.Encode(result.Definition!), pack.EncodedBytes(GidFor(name)).ToArray());
        }
    }

    [Fact]
    public void CliIsIndependentOfRepositoryLocationAndWorkingDirectory()
    {
        using var root = Prepare();
        Definition(root.Path, "Alpha");
        var expected = Pack(root.Path, "expected.zip");
        var other = root.Resolve("repository space");
        TemporaryFileSystem.Directory.CreateDirectory(other);
        TemporaryFileSystem.File.WriteAllText(Path.Combine(other, "global.json"), "{}");
        Definition(other, "Alpha");
        var working = Path.Combine(other, "nested working directory");
        TemporaryFileSystem.Directory.CreateDirectory(working);
        Assert.Equal(0, Cli(working, ["resources", "pack", "--out", "resources.zip"], TextWriter.Null, new StringWriter()));
        var actual = ScribeResourcePack.Open(Path.Combine(working, "resources.zip")).Manifest;
        Assert.Equal(expected.TotalSha256, actual.TotalSha256);
    }

    [Fact]
    public void IndependentFullPacksPreserveDigestAcrossThreadCultures()
    {
        using var root = Prepare();
        Definition(root.Path, "Alpha", expression: "$\"{1234:N0} {-5}\"");
        Definition(root.Path, "Beta");
        var culture = CultureInfo.CurrentCulture;
        var uiCulture = CultureInfo.CurrentUICulture;
        try
        {
            CultureInfo.CurrentCulture = new CultureInfo("en-US");
            CultureInfo.CurrentUICulture = CultureInfo.CurrentCulture;
            var first = Pack(root.Path, "first.zip");
            var second = Pack(root.Path, "second.zip");
            Assert.Equal(first.TotalSha256, second.TotalSha256);
            var selected = (CultureInfo)new CultureInfo("tr-TR").Clone();
            selected.NumberFormat.NegativeSign = "~";
            Assert.NotEqual(CultureInfo.CurrentCulture.TextInfo.ToUpper("i"), selected.TextInfo.ToUpper("i"));
            Assert.NotEqual((-5).ToString(CultureInfo.CurrentCulture), (-5).ToString(selected));
            CultureInfo.CurrentCulture = selected;
            CultureInfo.CurrentUICulture = selected;
            var third = Pack(root.Path, "third.zip");
            Assert.Equal(first.TotalSha256, third.TotalSha256);
            Assert.Same(selected, CultureInfo.CurrentCulture);
            Assert.Same(selected, CultureInfo.CurrentUICulture);
        }
        finally
        {
            CultureInfo.CurrentCulture = culture;
            CultureInfo.CurrentUICulture = uiCulture;
        }
    }

    private static ScribeResourcePackManifest Pack(string root, string output)
    {
        var result = ScribeResourceScriptPacker.Write(root, Path.Combine(root, output));
        Assert.Empty(result.Failures);
        Assert.NotNull(result.Manifest);
        return result.Manifest;
    }

    [Fact]
    public void EachFullPackLoadsCurrentProjectionFixtures()
    {
        using var root = new StatementProjectionTestRepository();
        TemporaryFileSystem.File.WriteAllText(Path.Combine(root.Path, "global.json"), "{}");
        Write(root.Path, "Alpha", """
            internal sealed class Alpha : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("digest", H("title"),
                    Blocks(new DocumentBlock.Section(H("Section"), Blocks(Describe.Lean(DescribeId.Create("claim"),
                        DeclarationHandle.Create("D5/S0/Test/Alpha.claim"), H("Claim"), StatementSource.FromLean(),
                        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("content"))), DescribeRole.Theorem))))));
            }
            """);
        void Fixture(int number) => root.WriteFixture("pilot", new StatementProjectionTestRepository.Pin(
            "Fixture.claim", "D5/S0/Test/Alpha.lean", StatementProjectionResolutionTests.Equality(number)));
        Fixture(1);
        var first = Pack(root.Path, "first.zip");
        Fixture(2);
        var second = Pack(root.Path, "second.zip");
        Assert.NotEqual(first.TotalSha256, second.TotalSha256);
        Assert.Equal(second.TotalSha256, Pack(root.Path, "third.zip").TotalSha256);
    }

    private static TemporaryRoot Prepare()
    {
        var root = new TemporaryRoot();
        TemporaryFileSystem.File.WriteAllText(root.Resolve("global.json"), "{}");
        TemporaryFileSystem.Directory.CreateDirectory(root.Resolve("Blueprint"));
        return root;
    }

    private static int Cli(string root, string[] arguments, TextWriter output, TextWriter error) =>
        ScribeCli.Run(typeof(ScribeResourcePack).Assembly, arguments, root, output, error);

    private static void AssertHostFailures(StringWriter error)
    {
        var lines = error.ToString().Split(Environment.NewLine, StringSplitOptions.RemoveEmptyEntries);
        Assert.Equal(2, lines.Length);
        Assert.Contains(PathFor("Alpha"), lines[0], StringComparison.Ordinal);
        Assert.Contains(PathFor("Beta"), lines[1], StringComparison.Ordinal);
        Assert.All(lines, line => Assert.StartsWith("DefinitionMissing:", line, StringComparison.Ordinal));
    }

    private static string PathFor(string name) => "Blueprint/" + GidFor(name) + ".scribe.cs";
    private static string GidFor(string name) => "D5/S0/Test/" + name;

    private static void Definition(string root, string name, string content = "content", string? expression = null)
    {
        Write(root, name, $$"""
            internal sealed class {{name}} : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H("title"), Blocks(Paragraph(Text({{expression ?? "\"" + content + "\""}})))));
            }
            """);
    }

    private static void Write(string root, string name, string body)
    {
        var full = Path.Combine(root, PathFor(name));
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(full)!);
        TemporaryFileSystem.File.WriteAllText(full, "using StrataLint.Scribe; using static StrataLint.Scribe.DefinitionDsl; " + body);
    }
}
