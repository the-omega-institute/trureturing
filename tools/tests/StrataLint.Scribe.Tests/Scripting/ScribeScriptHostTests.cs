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
        Assert.Equal(ScribeScriptFailureCode.Compilation, results[1].Failure!.Code);
        Assert.True(results[0].IsSuccess);
        Assert.True(results[2].IsSuccess);
    }

    private static void WriteDefinition(string root, string path, string name)
    {
        var gid = path["Blueprint/".Length..].Replace(".scribe.cs", string.Empty, StringComparison.Ordinal);
        File.WriteAllText(Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar)), $$"""
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
}
