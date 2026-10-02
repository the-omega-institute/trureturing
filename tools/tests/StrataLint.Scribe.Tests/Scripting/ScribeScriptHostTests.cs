using System.Reflection;
using StrataLint.Scribe;
using StrataLint.Scribe.Scripting;

namespace StrataLint.Scribe.Tests.Scripting;

public sealed class ScribeScriptHostTests
{
    [Fact]
    public void ExecutesOneSyntheticDefinition()
    {
        using var root = new TemporaryRoot();
        var path = "Blueprint/D5/S0/Test/Synthetic.scribe.cs";
        WriteDefinition(root.Path, path, "Synthetic");

        var result = ScribeScriptHost.Execute(root.Path, path);

        Assert.True(result.IsSuccess, result.Failure?.ToString());
        Assert.Equal("D5/S0/Test/Synthetic", result.Definition!.Document.Header.Gid.Value);
        Assert.Equal(path, result.Definition.SourcePath);
    }

    [Fact]
    public void BatchResultsArePathOrderedAndKeepFailures()
    {
        using var root = new TemporaryRoot();
        WriteDefinition(root.Path, "Blueprint/D5/S0/Test/Zed.scribe.cs", "Zed");
        WriteDefinition(root.Path, "Blueprint/D5/S0/Test/Alpha.scribe.cs", "Alpha");
        var broken = "Blueprint/D5/S0/Test/Broken.scribe.cs";
        File.WriteAllText(root.Resolve(broken), "namespace Synthetic; public sealed class Broken { }");

        var results = ScribeScriptHost.ExecuteBatch(root.Path, [broken, "Blueprint/D5/S0/Test/Zed.scribe.cs", "Blueprint/D5/S0/Test/Alpha.scribe.cs"]);

        Assert.Equal(
            new[] { "Blueprint/D5/S0/Test/Alpha.scribe.cs", broken, "Blueprint/D5/S0/Test/Zed.scribe.cs" },
            results.Select(static result => result.RelativePath));
        Assert.Equal(ScribeScriptFailureCode.DefinitionMissing, results[1].Failure!.Code);
        Assert.True(results[0].IsSuccess);
        Assert.True(results[2].IsSuccess);
    }

    [Theory]
    [InlineData("internal sealed class Invalid { MissingType field; }", ScribeScriptFailureCode.Compilation)]
    [InlineData("internal sealed class Empty { }", ScribeScriptFailureCode.DefinitionMissing)]
    [InlineData("internal sealed class Probe : IScribeDocumentDefinition { public DocumentDefinition Create() => throw new InvalidOperationException(\"fixture failure\"); }", ScribeScriptFailureCode.CreateFailed)]
    [InlineData("internal sealed class Probe : IScribeDocumentDefinition { public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(Header(\"D5/S0/Test/Other\", \"digest\"), H(\"title\"), Blocks(Paragraph(Text(\"content\"))))); }", ScribeScriptFailureCode.GidPathMismatch)]
    [InlineData("internal sealed class Probe : IScribeDocumentDefinition { public DocumentDefinition Create() { _ = DateTime.Now; return DocumentDefinition.Create(ScribeNode.Create(\"digest\", H(\"title\"), Blocks(Paragraph(Text(\"content\"))))); } }", ScribeScriptFailureCode.BannedSymbol)]
    [InlineData("internal sealed class Probe : IScribeDocumentDefinition { public DocumentDefinition Create() { string? value = null; _ = value.Length; return DocumentDefinition.Create(ScribeNode.Create(\"digest\", H(\"title\"), Blocks(Paragraph(Text(\"content\"))))); } }", ScribeScriptFailureCode.Compilation)]
    public void NamedFailuresCarrySourceAndReason(string body, ScribeScriptFailureCode expected)
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        Write(root, path, body);
        var result = ScribeScriptHost.Execute(root.Path, path);
        Assert.Equal(expected, result.Failure?.Code);
        Assert.Null(result.Definition);
        Assert.Contains(path, result.Failure!.ToString(), StringComparison.Ordinal);
        Assert.NotEmpty(result.Failure.Message);
    }

    [Fact]
    public void TwoDefinitionsAreRejectedBeforeCreate()
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        Write(root, path, "internal sealed class First : IScribeDocumentDefinition { public DocumentDefinition Create() => throw new InvalidOperationException(); } internal sealed class Second : IScribeDocumentDefinition { public DocumentDefinition Create() => throw new InvalidOperationException(); }");
        Assert.Equal(ScribeScriptFailureCode.MultipleDefinitions, ScribeScriptHost.Execute(root.Path, path).Failure?.Code);
    }

    [Theory]
    [InlineData("\"Blueprint/D5/S0/Test/Missing.scribe.cs\"", ScribeScriptFailureCode.SharedSourceMissing)]
    [InlineData("\"Outside/Shared.scribe.cs\"", ScribeScriptFailureCode.SharedSourceOutsideBlueprint)]
    [InlineData("\"Blueprint/../Outside/Shared.scribe.cs\"", ScribeScriptFailureCode.SharedSourceOutsideBlueprint)]
    [InlineData("\"Blueprint/D5/S0/Test/Probe.scribe.cs\"", ScribeScriptFailureCode.SharedSourceCycle)]
    [InlineData("nameof(Probe)", ScribeScriptFailureCode.SharedSourceArgument)]
    [InlineData("\"one\", \"two\"", ScribeScriptFailureCode.SharedSourceArgument)]
    public void SharedSourceDeclarationsFailClosed(string argument, ScribeScriptFailureCode expected)
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        Write(root, "Outside/Shared.scribe.cs", "internal sealed class Shared { }");
        Write(root, path, $"[ScribeSharedSource({argument})] internal sealed class Probe : IScribeDocumentDefinition {{ public DocumentDefinition Create() => throw new InvalidOperationException(); }}");
        Assert.Equal(expected, ScribeScriptHost.Execute(root.Path, path).Failure?.Code);
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void SharedSourcesRequireDeclarationsAndSupportTransitiveDependencies(bool declared, bool transitive)
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        const string shared = "Blueprint/D5/S0/Test/Shared.scribe.cs";
        Write(root, "Blueprint/D5/S0/Test/Leaf.scribe.cs", "internal static class Leaf { internal const string Value = \"content\"; }");
        Write(root, shared, (transitive ? "[ScribeSharedSource(\"Blueprint/D5/S0/Test/Leaf.scribe.cs\")] " : "") + "internal sealed class Shared : IScribeDocumentDefinition { internal static string Value => " + (transitive ? "Leaf.Value" : "\"content\"") + "; public DocumentDefinition Create() => throw new InvalidOperationException(\"shared definition must not execute\"); }");
        Write(root, path, (declared ? $"[ScribeSharedSource(\"{shared}\")] " : "") + "internal sealed class Probe : IScribeDocumentDefinition { public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(\"digest\", H(\"title\"), Blocks(Paragraph(Text(Shared.Value))))); }");
        var result = ScribeScriptHost.Execute(root.Path, path);
        if (declared) Assert.True(result.IsSuccess, result.Failure?.ToString());
        else Assert.Equal(ScribeScriptFailureCode.Compilation, result.Failure?.Code);
    }

    [Fact]
    public void ScriptsVerifyReturnsZeroForAnEquivalentSyntheticSet()
    {
        using var root = PrepareCommandRoot();
        const string path = "Blueprint/D5/S0/Test/First.scribe.cs";
        WriteDefinition(root.Path, path, "First");
        var output = new StringWriter();
        var error = new StringWriter();

        var exit = ScribeCli.Run(FixtureAssembly.Value, ["scripts", "verify", "--paths-from", "-"],
            root.Path, output, error, new StringReader(path));

        Assert.Equal(0, exit);
        Assert.Contains("paths=1 hostFailures=0 mismatches=0", output.ToString(), StringComparison.Ordinal);
        Assert.Empty(error.ToString());
    }

    [Fact]
    public void ScriptsVerifyNamesCanonicalMismatchAndInvalidArguments()
    {
        using var root = PrepareCommandRoot();
        const string path = "Blueprint/D5/S0/Test/First.scribe.cs";
        WriteDefinition(root.Path, path, "Changed");
        var output = new StringWriter();
        var error = new StringWriter();

        Assert.Equal(1, ScribeCli.Run(FixtureAssembly.Value, ["scripts", "verify", "--paths-from", "-"],
            root.Path, output, error, new StringReader(path)));
        Assert.Contains("CanonicalContentMismatch", error.ToString(), StringComparison.Ordinal);
        Assert.Equal(2, ScribeCli.Run(FixtureAssembly.Value, ["scripts", "verify", "--bad"],
            root.Path, TextWriter.Null, new StringWriter(), TextReader.Null));
    }

    private static TemporaryRoot PrepareCommandRoot()
    {
        var root = new TemporaryRoot();
        TemporaryFileSystem.File.WriteAllText(root.Resolve("global.json"), "{}");
        TemporaryFileSystem.Directory.CreateDirectory(root.Resolve("Blueprint"));
        return root;
    }

    private static void Write(TemporaryRoot root, string path, string body) =>
        TemporaryFileSystem.File.WriteAllText(root.Resolve(path),
            "using StrataLint.Scribe; using static StrataLint.Scribe.DefinitionDsl; namespace Synthetic; " + body);

    private static void WriteDefinition(string root, string path, string name)
    {
        var gid = path["Blueprint/".Length..].Replace(".scribe.cs", string.Empty, StringComparison.Ordinal);
        var fullPath = Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar));
        Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
        File.WriteAllText(fullPath, $$"""
            using static StrataLint.Scribe.DefinitionDsl;
            using StrataLint.Scribe;
            namespace Synthetic;
            internal sealed class {{name}}Document : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H("{{name}}"), Blocks(Paragraph(Text("content")))));
            }
            """);
    }

    private sealed class FixtureAssembly : Assembly
    {
        internal static Assembly Value { get; } = new FixtureAssembly();

        public override Type[] GetTypes() => [typeof(FirstDefinition)];
    }

    private sealed class FirstDefinition : IScribeDocumentDefinition
    {
        public DocumentDefinition Create()
        {
            const string path = "Blueprint/D5/S0/Test/First.scribe.cs";
            return DocumentDefinition.Create(
                ScribeNode.Create("digest", DefinitionDsl.H("First"),
                    DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("content"))),
                    sourcePath: path),
                sourcePath: path);
        }
    }
}
