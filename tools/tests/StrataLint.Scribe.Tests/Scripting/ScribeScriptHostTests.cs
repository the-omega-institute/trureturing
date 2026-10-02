using System.Collections.Immutable;
using System.Reflection;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Diagnostics;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeScriptHostTests
{
    [Theory]
    [InlineData(null)]
    [InlineData("   ")]
    [InlineData("NET10_0;bad-symbol")]
    public void InvalidDefineConstantsReturnHostConfiguration(string? constants)
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        WriteDefinition(root.Path, path, "Probe");
        var result = ScribeScriptHost.ExecuteWithDefineConstants(root.Path, path, constants);
        Assert.Equal(ScribeScriptFailureCode.HostConfiguration, result.Failure?.Code);
        Assert.Null(result.Definition);
    }

    [Fact]
    public void EscapedNamespaceUsesMetadataNames()
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        Write(root, path, "namespace @event.@class; internal sealed class Probe : IScribeDocumentDefinition { public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(\"digest\", H(\"title\"), Blocks(Paragraph(Text(\"content\"))))); }");
        var result = ScribeScriptHost.Execute(root.Path, path);
        Assert.True(result.IsSuccess, result.Failure?.ToString());
    }

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
    public void ExecutesOneRecordClassDefinition()
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        Write(root, path, """
            internal sealed record class Probe : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H("title"), Blocks(Paragraph(Text("content")))));
            }
            """);

        var result = ScribeScriptHost.Execute(root.Path, path);

        Assert.True(result.IsSuccess, result.Failure?.ToString());
        Assert.Equal("D5/S0/Test/Probe", result.Definition!.Document.Header.Gid.Value);
        Assert.Equal(path, result.Definition.SourcePath);
    }

    [Fact]
    public void FileReadInDefinitionIsRejectedAsDisallowedSymbol()
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        var input = root.Resolve("input.txt");
        File.WriteAllText(input, "content");
        Write(root, path, $$"""
            internal sealed class Probe : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H(File.ReadAllText("{{input.Replace("\\", "\\\\", StringComparison.Ordinal)}}")), Blocks(Paragraph(Text("content")))));
            }
            """);

        var result = ScribeScriptHost.Execute(root.Path, path);

        Assert.True(result.Failure?.Code == ScribeScriptFailureCode.DisallowedSymbol, result.Failure?.ToString());
        Assert.True(result.Failure?.Message.Contains("System.IO.File.ReadAllText", StringComparison.Ordinal), result.Failure?.ToString());
    }

    [Theory]
    [InlineData("Environment.GetEnvironmentVariable(\"SCRIBE_INPUT\")")]
    [InlineData("Directory.GetFiles(\".\")")]
    [InlineData("typeof(Probe).Assembly")]
    [InlineData("System.Diagnostics.Process.GetCurrentProcess()")]
    [InlineData("new System.Net.Http.HttpClient()")]
    [InlineData("DateTime.Today")]
    [InlineData("System.Globalization.CultureInfo.CurrentCulture")]
    [InlineData("ScribeScriptHost.Execute(\".\", \"Blueprint/D5/S0/Test/Other.scribe.cs\")")]
    [InlineData("dynamic value = \"input\"; _ = value.ToString()")]
    public void ExternalChannelsAreRejectedByTheAllowlist(string expression)
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        var statement = expression.StartsWith("dynamic ", StringComparison.Ordinal)
            ? $"{expression};"
            : $"_ = {expression};";
        Write(root, path, $$"""
            internal sealed class Probe : IScribeDocumentDefinition
            {
                public DocumentDefinition Create()
                {
                    {{statement}}
                    return DocumentDefinition.Create(
                        ScribeNode.Create("digest", H("title"), Blocks(Paragraph(Text("content")))));
                }
            }
            """);

        var result = ScribeScriptHost.Execute(root.Path, path);

        Assert.True(result.Failure?.Code == ScribeScriptFailureCode.DisallowedSymbol, result.Failure?.ToString());
    }

    [Fact]
    public void SharedSourceExternalChannelsAreRejected()
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        const string shared = "Blueprint/D5/S0/Test/Shared.scribe.cs";
        Write(root, shared, "internal static class Shared { internal static string Value => Environment.GetEnvironmentVariable(\"SCRIBE_INPUT\") ?? \"\"; }");
        Write(root, path, $$"""
            [ScribeSharedSource("{{shared}}")]
            internal sealed class Probe : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H(Shared.Value), Blocks(Paragraph(Text("content")))));
            }
            """);

        var result = ScribeScriptHost.Execute(root.Path, path);

        Assert.True(result.Failure?.Code == ScribeScriptFailureCode.DisallowedSymbol, result.Failure?.ToString());
    }

    [Theory]
    [InlineData(null)]
    [InlineData("")]
    [InlineData("X:NotAnEntry")]
    public void AllowlistConfigurationFailsClosed(string? contents)
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        WriteDefinition(root.Path, path, "Probe");
        var allowlistPath = Path.Combine(AppContext.BaseDirectory, "Scripting", "ScribeScriptAllowlist.txt");
        var original = File.ReadAllText(allowlistPath);
        try
        {
            if (contents is null) File.Delete(allowlistPath);
            else File.WriteAllText(allowlistPath, contents);

            var result = ScribeScriptHost.Execute(root.Path, path);

            Assert.Equal(ScribeScriptFailureCode.HostConfiguration, result.Failure?.Code);
        }
        finally
        {
            File.WriteAllText(allowlistPath, original);
        }
    }

    [Fact]
    public void InvalidPathHasANamedFailure()
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/../Probe.scribe.cs";

        var result = ScribeScriptHost.Execute(root.Path, path);

        Assert.Equal(ScribeScriptFailureCode.InvalidPath, result.Failure?.Code);
        Assert.Equal(path, result.Failure!.RelativePath);
        Assert.Null(result.Definition);
    }

    [Fact]
    public void MissingAnalyzerHasAHostConfigurationFailure()
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        WriteDefinition(root.Path, path, "Probe");
        var execute = typeof(ScribeScriptHost).GetMethod("ExecuteCore", BindingFlags.NonPublic | BindingFlags.Static)!;

        var result = Assert.IsType<ScribeScriptResult>(execute.Invoke(null,
            [root.Path, path, ImmutableArray<MetadataReference>.Empty, ImmutableArray<DiagnosticAnalyzer>.Empty]));

        Assert.Equal(ScribeScriptFailureCode.HostConfiguration, result.Failure?.Code);
        Assert.Equal(path, result.Failure!.RelativePath);
        Assert.Equal("banned API analyzer is unavailable", result.Failure.Message);
        Assert.Null(result.Definition);
    }

    [Fact]
    public void LockedSourceHasASourceReadFailure()
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        WriteDefinition(root.Path, path, "Probe");
        using var source = new FileStream(root.Resolve(path), FileMode.Open, FileAccess.Read, FileShare.None);

        var result = ScribeScriptHost.Execute(root.Path, path);

        Assert.Equal(ScribeScriptFailureCode.SourceRead, result.Failure?.Code);
        Assert.Equal(path, result.Failure!.RelativePath);
        Assert.NotEmpty(result.Failure.Message);
        Assert.Null(result.Definition);
    }

    [Fact]
    public void BatchResultsArePathOrderedAndKeepFailures()
    {
        using var root = new TemporaryRoot();
        WriteDefinition(root.Path, "Blueprint/D5/S0/Test/Zed.scribe.cs", "Zed");
        WriteDefinition(root.Path, "Blueprint/D5/S0/Test/Alpha.scribe.cs", "Alpha");
        var broken = "Blueprint/D5/S0/Test/Broken.scribe.cs";
        File.WriteAllText(root.Resolve(broken), "public sealed class Broken { }");

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

    [Fact]
    public void ClassAndRecordClassDefinitionsAreRejectedBeforeCreate()
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        Write(root, path, """
            internal sealed class First : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => throw new InvalidOperationException();
            }
            internal sealed record class Second : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => throw new InvalidOperationException();
            }
            """);

        var result = ScribeScriptHost.Execute(root.Path, path);

        Assert.Equal(ScribeScriptFailureCode.MultipleDefinitions, result.Failure?.Code);
        Assert.Null(result.Definition);
    }

    [Fact]
    public void FrameworkConditionalBannedSymbolIsRejected()
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        Write(root, path, """
            internal sealed class Probe : IScribeDocumentDefinition
            {
                public DocumentDefinition Create()
                {
            #if NET10_0_OR_GREATER
                    _ = DateTime.Now;
            #endif
                    return DocumentDefinition.Create(
                        ScribeNode.Create("digest", H("title"), Blocks(Paragraph(Text("content")))));
                }
            }
            """);

        Assert.Equal(ScribeScriptFailureCode.BannedSymbol,
            ScribeScriptHost.Execute(root.Path, path).Failure?.Code);
    }

    [Fact]
    public void FieldInitializationUsesTheSuppliedRepositoryRoot()
    {
        using var repository = new StatementProjectionTestRepository(
            new StatementProjectionTestRepository.Pin("D5.S0.Test.Probe.claim", "D5/S0/Test/Probe.lean",
                StatementProjectionResolutionTests.Equality(1)));
        Assert.NotEqual(System.IO.Path.GetFullPath(Environment.CurrentDirectory), repository.Path);
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        var fullPath = System.IO.Path.Combine(repository.Path, path);
        Directory.CreateDirectory(System.IO.Path.GetDirectoryName(fullPath)!);
        File.WriteAllText(fullPath, """
            using StrataLint.Engine;
            using StrataLint.Scribe;
            using static StrataLint.Scribe.DefinitionDsl;
            internal sealed class Probe : IScribeDocumentDefinition
            {
                private readonly DocumentBlock.Describe statement = Describe.Lean(
                    DescribeId.Create("claim"), DeclarationHandle.Create("D5/S0/Test/Probe.claim"),
                    H("Claim"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("content"))), DescribeRole.Theorem);
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H("Probe"), Blocks(statement)));
            }
            """);
        var discovered = Assert.Single(DocumentDefinitions.Discover(new FieldDefinitionAssembly(), repository.Path));

        var result = ScribeScriptHost.Execute(repository.Path, path);

        Assert.True(result.IsSuccess, result.Failure?.ToString());
        Assert.Equal(ScribeResourceCodec.Encode(discovered), ScribeResourceCodec.Encode(result.Definition!));
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
    public void RecordClassSharedSourceDeclarationIsUsed()
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        const string shared = "Blueprint/D5/S0/Test/Shared.scribe.cs";
        Write(root, shared, """
            internal sealed class Shared : IScribeDocumentDefinition
            {
                internal const string Value = "shared content";
                public DocumentDefinition Create() => throw new InvalidOperationException();
            }
            """);
        Write(root, path, $$"""
            [ScribeSharedSource("{{shared}}")]
            internal sealed record class Probe : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H("title"), Blocks(Paragraph(Text(Shared.Value)))));
            }
            """);

        var result = ScribeScriptHost.Execute(root.Path, path);

        Assert.True(result.IsSuccess, result.Failure?.ToString());
        Assert.Equal(path, result.Definition!.SourcePath);
        Assert.Equal(ScribeResourceCodec.Encode(DocumentDefinition.Create(
            ScribeNode.Create("digest", DefinitionDsl.H("title"),
                DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("shared content"))),
                sourcePath: path), sourcePath: path)), ScribeResourceCodec.Encode(result.Definition));
    }

    [Fact]
    public void UnrelatedAttributeSuffixDoesNotDeclareSharedSource()
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        Write(root, path, """
            internal sealed class OtherScribeSharedSourceAttribute(string path) : Attribute
            {
                public string Path { get; } = path;
            }
            [OtherScribeSharedSource("Outside/Shared.scribe.cs")]
            internal sealed class Probe : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H("title"), Blocks(Paragraph(Text("content")))));
            }
            """);

        var result = ScribeScriptHost.Execute(root.Path, path);

        Assert.True(result.IsSuccess, result.Failure?.ToString());
    }

    [Theory]
    [InlineData("ScribeSharedSource")]
    [InlineData("ScribeSharedSourceAttribute")]
    [InlineData("StrataLint.Scribe.ScribeSharedSource")]
    [InlineData("StrataLint.Scribe.ScribeSharedSourceAttribute")]
    [InlineData("global::StrataLint.Scribe.ScribeSharedSource")]
    [InlineData("global::StrataLint.Scribe.ScribeSharedSourceAttribute")]
    public void ExactSharedSourceAttributeNamesAreRecognized(string name)
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        Write(root, path, $"[{name}(\"Blueprint/D5/S0/Test/Missing.scribe.cs\")] internal sealed class Probe {{ }}");

        Assert.Equal(ScribeScriptFailureCode.SharedSourceMissing,
            ScribeScriptHost.Execute(root.Path, path).Failure?.Code);
    }

    [Fact]
    public void GenericAliasQualifierDoesNotDeclareSharedSource()
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        Write(root, path,
            "[global::StrataLint<int>.Scribe.ScribeSharedSource(\"Outside/Shared.scribe.cs\")] internal sealed class Probe { }");

        Assert.Equal(ScribeScriptFailureCode.Compilation,
            ScribeScriptHost.Execute(root.Path, path).Failure?.Code);
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

    [Fact]
    public void ScriptsVerifyRejectsAnEmptySelection()
    {
        using var root = PrepareCommandRoot();
        var output = new StringWriter();
        var error = new StringWriter();

        var exit = ScribeCli.Run(FixtureAssembly.Value, ["scripts", "verify", "--paths-from", "-"],
            root.Path, output, error, new StringReader(string.Empty));

        Assert.Equal(1, exit);
        Assert.Contains("EmptyScriptSelection", error.ToString(), StringComparison.Ordinal);
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
            "using StrataLint.Scribe; using static StrataLint.Scribe.DefinitionDsl; " + body);

    private static void WriteDefinition(string root, string path, string name)
    {
        var gid = path["Blueprint/".Length..].Replace(".scribe.cs", string.Empty, StringComparison.Ordinal);
        var fullPath = Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar));
        Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
        File.WriteAllText(fullPath, $$"""
            using static StrataLint.Scribe.DefinitionDsl;
            using StrataLint.Scribe;
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

    private sealed class FieldDefinitionAssembly : Assembly
    {
        public override Type[] GetTypes() => [typeof(FieldDefinition)];
    }

    private sealed class FieldDefinition : IScribeDocumentDefinition
    {
        private readonly DocumentBlock.Describe statement = Describe.Lean(
            DescribeId.Create("claim"), DeclarationHandle.Create("D5/S0/Test/Probe.claim"),
            DefinitionDsl.H("Claim"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("content"))), DescribeRole.Theorem);

        public DocumentDefinition Create()
        {
            const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
            return DocumentDefinition.Create(
                ScribeNode.Create("digest", DefinitionDsl.H("Probe"), DefinitionDsl.Blocks(statement),
                    sourcePath: path), sourcePath: path);
        }
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
