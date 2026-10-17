using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;
using System.Globalization;
using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Diagnostics;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Scribe.Tests;

[Collection("Process environment")]
public sealed class ScribeScriptHostTests
{
    private const string DiagnosticPrefix = "STRATALINT_SCRIBE_LOAD_DIAGNOSTIC_";

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
        Assert.True(result.Failure?.Message.Contains("M:System.IO.File.ReadAllText(System.String)", StringComparison.Ordinal), result.Failure?.ToString());
    }

    [Theory]
    [InlineData("Environment.GetEnvironmentVariable(\"SCRIBE_INPUT\")", "M:System.Environment.GetEnvironmentVariable(System.String)")]
    [InlineData("Directory.GetFiles(\".\")", "M:System.IO.Directory.GetFiles(System.String)")]
    [InlineData("typeof(Probe).Assembly", "P:System.Type.Assembly")]
    [InlineData("System.Diagnostics.Process.GetCurrentProcess()", "M:System.Diagnostics.Process.GetCurrentProcess")]
    [InlineData("new System.Net.Http.HttpClient()", "M:System.Net.Http.HttpClient.#ctor")]
    [InlineData("DateTime.Today", "P:System.DateTime.Today")]
    [InlineData("System.Globalization.CultureInfo.CurrentCulture", "P:System.Globalization.CultureInfo.CurrentCulture")]
    [InlineData("ScribeScriptHost.Execute(\".\", \"Blueprint/D5/S0/Test/Other.scribe.cs\")", "M:StrataLint.Scribe.ScribeScriptHost.Execute(System.String,System.String)")]
    [InlineData("dynamic value = \"input\"; _ = value.ToString()", "T:System.Object")]
    public void ExternalChannelsAreRejectedByTheAllowlist(string expression, string id)
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

        ScribeScriptAdmissionTests.Reject(result, id);
    }

    [Fact]
    public void AllowlistedEnumerableDefinitionExecutes()
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        Write(root, path, "internal sealed class Probe : IScribeDocumentDefinition { public DocumentDefinition Create() { var values = Enumerable.Repeat(1, 1).ToArray(); return DocumentDefinition.Create(ScribeNode.Create(\"digest\", H(values.Length.ToString(System.Globalization.CultureInfo.InvariantCulture)), Blocks(Paragraph(Text(\"content\"))))); } }");

        var result = ScribeScriptHost.Execute(root.Path, path);

        Assert.True(result.IsSuccess, result.Failure?.ToString());
    }

    [Theory]
    [InlineData(null)]
    [InlineData("")]
    [InlineData("X:NotAnEntry")]
    [InlineData("T:System.String\nT:System.String")]
    [InlineData("T:Missing.Type")]
    [InlineData("M:System.Linq.Enumerable::MissingMember")]
    public void AllowlistConfigurationFailsClosed(string? contents)
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        WriteDefinition(root.Path, path, "Probe");
        var allowlistPath = root.Resolve("Scripting/ScribeScriptAllowlist.txt");
        if (contents is not null) TemporaryFileSystem.File.WriteAllText(allowlistPath, contents);

        var result = ScribeScriptHost.ExecuteWithAllowlistPath(root.Path, path, allowlistPath);

        Assert.Equal(ScribeScriptFailureCode.HostConfiguration, result.Failure?.Code);
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
    public void TypeLoadFailureCarriesSourcePath()
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        WriteDefinition(root.Path, path, "Probe");

        var result = ScribeScriptHost.ExecuteWithEntryType(root.Path, path, "Missing.Entry");

        Assert.Equal(ScribeScriptFailureCode.TypeLoad, result.Failure?.Code);
        Assert.Contains(path, result.Failure!.ToString(), StringComparison.Ordinal);
        Assert.Null(result.Definition);
    }

    [Fact]
    public void TypeLoadDiagnosticReconstructsTheCompleteLiveImage()
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        WriteDefinition(root.Path, path, "Probe");
        var output = new StringWriter();
        var result = ScribeScriptHost.ExecuteWithEntryType(root.Path, path, "Missing.Entry", output);

        Assert.Equal(ScribeScriptFailureCode.TypeLoad, result.Failure?.Code);
        Assert.Null(result.Definition);
        var frame = Assert.Single(ReadFrames(output.ToString()));
        AssertFrame(frame, path, "Missing.Entry", result);
        Assert.Single(frame.Chunks);
    }

    [Fact]
    public async Task ConcurrentLoadFailuresKeepSeparatelyAttributableFrames()
    {
        using var root = new TemporaryRoot();
        const string first = "Blueprint/D5/S0/Test/First.scribe.cs";
        const string second = "Blueprint/D5/S0/Test/Second.scribe.cs";
        var allowlist = WriteInvalidLayout(root, first, "First");
        WriteInvalidLayout(root, second, "Second");
        using var overlap = new Barrier(2);
        using var output = new OverlappingWriter(overlap);

        // Both real GetType failures reach BEGIN before either can emit fields.
        // Entry selection, exception filtering and the load path are unchanged.
        var results = await Task.WhenAll(
            Task.Run(() => ScribeScriptHost.ExecuteWithAllowlistPath(root.Path, first, allowlist, output)),
            Task.Run(() => ScribeScriptHost.ExecuteWithAllowlistPath(root.Path, second, allowlist, output)));

        var wire = output.ToString();
        Assert.All(wire.Split('\n', StringSplitOptions.RemoveEmptyEntries).Take(2),
            line => Assert.StartsWith(DiagnosticPrefix + "BEGIN ", line, StringComparison.Ordinal));
        var frames = ReadFrames(wire).ToDictionary(frame => Decode(frame.Fields["source_utf8_base64"]));
        Assert.Equal(2, frames.Count);
        AssertFrame(frames[first], first, "First`1", results[0]);
        AssertFrame(frames[second], second, "Second`1", results[1]);
        Assert.NotEqual(frames[first].Fields["image_sha256"], frames[second].Fields["image_sha256"]);
        Assert.All(frames.Values, frame => Assert.True(frame.Chunks.Count > 1));
    }

    [Fact]
    public async Task InvocationSinkDoesNotDivertAnUnrelatedLoadFailureFromStandardError()
    {
        using var root = new TemporaryRoot();
        const string scoped = "Blueprint/D5/S0/Test/Scoped.scribe.cs";
        const string ordinary = "Blueprint/D5/S0/Test/Ordinary.scribe.cs";
        var allowlist = WriteInvalidLayout(root, scoped, "Scoped");
        WriteInvalidLayout(root, ordinary, "Ordinary");
        using var overlap = new Barrier(2);
        using var output = new OverlappingWriter(overlap);
        using var error = new OverlappingWriter(overlap);
        var previous = Console.Error;
        ScribeScriptResult[] results;
        try
        {
            Console.SetError(error);
            results = await Task.WhenAll(
                Task.Run(() => ScribeScriptHost.ExecuteWithAllowlistPath(root.Path, scoped, allowlist, output)),
                Task.Run(() => ScribeScriptHost.ExecuteWithAllowlistPath(root.Path, ordinary, allowlist)));
        }
        finally
        {
            Console.SetError(previous);
        }

        AssertFrame(Assert.Single(ReadFrames(output.ToString())), scoped, "Scoped`1", results[0]);
        AssertFrame(Assert.Single(ReadFrames(error.ToString())), ordinary, "Ordinary`1", results[1]);
    }

    [Fact]
    public void IncompleteDiagnosticKeepsTheOriginalTypeLoadFailure()
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        WriteDefinition(root.Path, path, "Probe");
        using var output = new FailOnceWriter();

        var result = ScribeScriptHost.ExecuteWithEntryType(root.Path, path, "Missing.Entry", output);

        Assert.Equal(ScribeScriptFailureCode.TypeLoad, result.Failure?.Code);
        Assert.Contains("Missing.Entry", result.Failure!.Message, StringComparison.Ordinal);
        Assert.Null(result.Definition);
        Assert.Contains(DiagnosticPrefix + "INCOMPLETE ", output.ToString(), StringComparison.Ordinal);
        Assert.Throws<FormatException>(() => ReadFrames(output.ToString()));
    }

    [Fact]
    public void ReconstructionRejectsBrokenBoundariesChunksDigestsAndIncompleteEvidence()
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        WriteDefinition(root.Path, path, "Probe");
        using var output = new StringWriter();
        ScribeScriptHost.ExecuteWithEntryType(root.Path, path, "Missing.Entry", output);
        var wire = output.ToString();
        var lines = wire.Split('\n', StringSplitOptions.RemoveEmptyEntries);
        var chunk = Assert.Single(lines, line => line.StartsWith(DiagnosticPrefix + "CHUNK ", StringComparison.Ordinal));
        var field = lines.First(line => line.Contains(" image_sha256=", StringComparison.Ordinal));
        var corruptChunk = chunk[..(chunk.IndexOf("base64=", StringComparison.Ordinal) + 7)]
            + Convert.ToBase64String(new byte[ParseChunk(chunk.Split(' ', 3)[2]).Bytes.Length]);
        string Without(string line) => wire.Replace(line + "\n", "", StringComparison.Ordinal);
        string Replace(string oldValue, string newValue) => wire.Replace(oldValue, newValue, StringComparison.Ordinal);
        var corruptions = new[]
        {
            Without(lines[0]), Without(lines[^1]), Without(chunk),
            Without(lines.First(line => line.Contains(" source_utf8_base64=", StringComparison.Ordinal))),
            Without(lines.First(line => line.Contains(" reference_0_mvid=", StringComparison.Ordinal))),
            wire + lines[0] + "\n", Replace(lines[0], lines[0] + "\n" + lines[0]),
            Replace(chunk, chunk + "\n" + chunk), Replace(chunk, corruptChunk),
            Replace("index=0", "index=1"), Replace("offset=0", "offset=1"),
            Replace(" length=", " length=1"), Replace("chunks=1", "chunks=2"),
            Replace(field, field[..(field.LastIndexOf('=') + 1)] + new string('0', 64)),
            Replace("payload_complete=true", "payload_complete=false"),
            Replace("failure_exception_complete=true", "failure_exception_complete=false"),
            Replace(field, field + "\n" + field),
            Replace("_END ", "_INCOMPLETE "),
        };
        foreach (var corrupted in corruptions)
            Assert.Throws<FormatException>(() => ReadFrames(corrupted));
        Assert.Equal(2, ReadFrames(wire + wire.Replace(lines[0].Split(' ')[1],
            "capture=1-1", StringComparison.Ordinal)).Count);
    }

    [Fact]
    public void CurrentMarkdownLoadSampleIsFiniteAndKeepsFailureSemantics()
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Synthetic/CurrentMarkdown.scribe.cs";
        Write(root, path, "namespace StrataLint.Scribe.Blueprint.D5.S0.Synthetic; " + """
            internal sealed class CurrentMarkdown : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H("Current Markdown"), Blocks(Paragraph(Text("content")))));
            }
            """);

        // One bounded sample: two sequential loads, one collection checkpoint, and
        // two concurrent loads through the ordinary batch path.
        for (var index = 0; index < 2; index++)
            Assert.True(ScribeScriptHost.Execute(root.Path, path).IsSuccess);
        GC.Collect();
        GC.WaitForPendingFinalizers();
        GC.Collect();
        var results = ScribeScriptHost.ExecuteBatch(root.Path, [path, path]);
        Assert.Equal(2, results.Length);
        Assert.All(results, result => Assert.True(result.IsSuccess, result.Failure?.ToString()));
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
    [InlineData("internal sealed class Probe : IScribeDocumentDefinition { public DocumentDefinition Create() { _ = DateTime.Now; return DocumentDefinition.Create(ScribeNode.Create(\"digest\", H(\"title\"), Blocks(Paragraph(Text(\"content\"))))); } }", ScribeScriptFailureCode.DisallowedSymbol)]
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

        ScribeScriptAdmissionTests.Reject(ScribeScriptHost.Execute(root.Path, path), "P:System.DateTime.Now");
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
        var discovered = StatementProjectionFixtureLoader.WithRepositoryRoot(repository.Path, () => new FieldDefinition().Create());

        var result = ScribeScriptHost.Execute(repository.Path, path);

        Assert.True(result.IsSuccess, result.Failure?.ToString());
        Assert.Equal(ScribeResourceCodec.Encode(discovered), ScribeResourceCodec.Encode(result.Definition!));
    }

    [Fact]
    public void ReferenceToAnotherDefinitionFileFailsToCompile()
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        Write(root, "Blueprint/D5/S0/Test/Other.scribe.cs",
            "internal static class Other { internal const string Value = \"content\"; }");
        Write(root, path, "internal sealed class Probe : IScribeDocumentDefinition { public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(\"digest\", H(\"title\"), Blocks(Paragraph(Text(Other.Value))))); }");

        var result = ScribeScriptHost.Execute(root.Path, path);

        Assert.Equal(ScribeScriptFailureCode.Compilation, result.Failure?.Code);
        Assert.Contains("Other", result.Failure!.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SharedSourceDeclarationDoesNotCompile()
    {
        using var root = new TemporaryRoot();
        const string path = "Blueprint/D5/S0/Test/Probe.scribe.cs";
        Write(root, "Blueprint/D5/S0/Test/Other.scribe.cs", "internal static class Other { }");
        Write(root, path, "[ScribeSharedSource(\"Blueprint/D5/S0/Test/Other.scribe.cs\")] internal sealed class Probe : IScribeDocumentDefinition { public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(\"digest\", H(\"title\"), Blocks(Paragraph(Text(\"content\"))))); }");

        Assert.Equal(ScribeScriptFailureCode.Compilation, ScribeScriptHost.Execute(root.Path, path).Failure?.Code);
    }

    [Fact]
    public void ScriptsVerifyExecutesTheSelectedSyntheticDefinition()
    {
        using var root = PrepareCommandRoot();
        const string path = "Blueprint/D5/S0/Test/First.scribe.cs";
        WriteDefinition(root.Path, path, "First");
        var output = new StringWriter();
        var error = new StringWriter();

        var exit = ScribeCli.Run(["scripts", "verify", "--paths-from", "-"],
            root.Path, output, error, new StringReader(path));

        Assert.Equal(0, exit);
        Assert.Contains("paths=1 hostFailures=0", output.ToString(), StringComparison.Ordinal);
        Assert.Empty(error.ToString());
    }

    [Fact]
    public void ScriptsVerifyRejectsInvalidArguments()
    {
        using var root = PrepareCommandRoot();
        Assert.Equal(2, ScribeCli.Run(["scripts", "verify", "--bad"],
            root.Path, TextWriter.Null, new StringWriter(), TextReader.Null));
    }

    [Fact]
    public void ScriptsVerifyRejectsAnEmptySelection()
    {
        using var root = PrepareCommandRoot();
        var output = new StringWriter();
        var error = new StringWriter();

        var exit = ScribeCli.Run(["scripts", "verify", "--paths-from", "-"],
            root.Path, output, error, new StringReader(string.Empty));

        Assert.Equal(1, exit);
        Assert.Contains("EmptyScriptSelection", error.ToString(), StringComparison.Ordinal);
    }

    private static TemporaryRoot PrepareCommandRoot()
    {
        var root = new TemporaryRoot(sdkConfiguration: true);
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

    private static string Decode(string value) => Encoding.UTF8.GetString(Convert.FromBase64String(value));

    private static string WriteInvalidLayout(TemporaryRoot root, string path, string name)
    {
        // Roslyn emits this image; the CLR rejects explicit layout on a generic type.
        Write(root, path, $$"""
            [System.Runtime.InteropServices.StructLayout(System.Runtime.InteropServices.LayoutKind.Explicit)]
            internal sealed class {{name}}<T> : IScribeDocumentDefinition
            {
                public const string Padding = "{{new string('x', 4096)}}";
                public DocumentDefinition Create() => throw new InvalidOperationException("must not execute");
            }
            """);
        var table = root.Resolve("Scripting/InvalidLayoutAllowlist.txt");
        TemporaryFileSystem.File.WriteAllText(table,
            File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "Scripting", "ScribeScriptAllowlist.txt")) + "\n" + """
            T:System.Runtime.InteropServices.StructLayoutAttribute
            M:System.Runtime.InteropServices.StructLayoutAttribute.#ctor(System.Runtime.InteropServices.LayoutKind)
            T:System.Runtime.InteropServices.LayoutKind
            F:System.Runtime.InteropServices.LayoutKind.Explicit
            """);
        return table;
    }

    private static void AssertFrame(DiagnosticFrame frame, string path, string entry, ScribeScriptResult result)
    {
        Assert.Equal(ScribeScriptFailureCode.TypeLoad, result.Failure?.Code);
        Assert.False(result.IsSuccess);
        Assert.Null(result.Definition);
        Assert.Equal(path, result.Failure!.RelativePath);
        Assert.Contains(path, result.Failure.ToString(), StringComparison.Ordinal);
        Assert.Equal(path, Decode(frame.Fields["source_utf8_base64"]));
        Assert.Equal(entry, Decode(frame.Fields["entry_utf8_base64"]));
        Assert.Equal("TypeLoad", frame.Fields["failure_code"]);
        var exception = Decode(frame.Fields["failure_exception_utf8_base64"]);
        Assert.Contains("TypeLoadException", exception, StringComparison.Ordinal);
        Assert.Contains(result.Failure.Message, exception, StringComparison.Ordinal);
        Assert.Contains(entry, result.Failure.Message, StringComparison.Ordinal);
        Assert.Equal("true", frame.Fields["load_context_collectible"]);
        // Names describe contexts; unnamed contexts do not have unique name identities.
        Assert.Equal(frame.Fields["load_context_name"], frame.Fields["loaded_context_name"]);
        Assert.Equal("System.Private.CoreLib.dll", Path.GetFileName(frame.Fields["managed_core_library_path"]));
        Assert.False(frame.Fields.ContainsKey("coreclr_path"));
        using var pe = new PEReader(new MemoryStream(frame.Image, writable: false));
        var metadata = pe.GetMetadataReader();
        Assert.Equal(frame.Fields["image_mvid"], metadata.GetGuid(metadata.GetModuleDefinition().Mvid).ToString("D"));
        Assert.Equal(frame.Fields["image_mvid"], frame.Fields["loaded_assembly_mvid"]);
        Assert.NotEmpty(frame.Fields["reference_0_identity"]);
        Assert.NotEqual("<unavailable>", frame.Fields["reference_0_mvid"]);
    }

    private static List<DiagnosticFrame> ReadFrames(string wire)
    {
        var active = new Dictionary<string, DiagnosticFrame>(StringComparer.Ordinal);
        var seen = new HashSet<string>(StringComparer.Ordinal);
        var complete = new List<DiagnosticFrame>();
        foreach (var line in wire.Split('\n', StringSplitOptions.RemoveEmptyEntries).Select(line => line.TrimEnd('\r')))
        {
            var parts = line.Split(' ', 3);
            Require(parts.Length == 3 && parts[0].StartsWith(DiagnosticPrefix, StringComparison.Ordinal)
                && parts[1].StartsWith("capture=", StringComparison.Ordinal), "invalid diagnostic line");
            var id = parts[1]["capture=".Length..];
            var coordinates = id.Split('-');
            Require(coordinates.Length == 2 && coordinates.All(value => long.TryParse(value, NumberStyles.None,
                CultureInfo.InvariantCulture, out var number) && number > 0), "invalid process/sequence capture id");
            var kind = parts[0][DiagnosticPrefix.Length..];
            Require(kind != "INCOMPLETE", "explicitly incomplete diagnostic");
            if (kind == "BEGIN")
            {
                Require(parts[2] == "version=2" && seen.Add(id), "duplicate or unsupported frame");
                active.Add(id, new DiagnosticFrame());
                continue;
            }
            Require(active.TryGetValue(id, out _), "line outside complete frame boundaries");
            var frame = active[id];
            switch (kind)
            {
                case "FIELD":
                    var field = parts[2].Split('=', 2);
                    Require(field.Length == 2 && frame.Fields.TryAdd(field[0], field[1]), "duplicate or invalid field");
                    break;
                case "CHUNK":
                    var chunk = ParseChunk(parts[2]);
                    Require(chunk.Index == frame.Chunks.Count && chunk.Offset == frame.Chunks.Sum(item => item.Bytes.Length),
                        "noncontiguous chunk index or offset");
                    frame.Chunks.Add(chunk);
                    break;
                case "END":
                    Require(parts[2].StartsWith("chunks=", StringComparison.Ordinal), "invalid END");
                    Require(Number(parts[2]["chunks=".Length..]) == frame.Chunks.Count, "chunk count mismatch");
                    Require(frame.Fields.GetValueOrDefault("payload_complete") == "true"
                        && frame.Fields.GetValueOrDefault("failure_exception_complete") == "true"
                        && !frame.Fields.ContainsKey("payload_incomplete_reason"), "incomplete payload or exception");
                    var requiredFields = new[]
                    {
                        "source_utf8_base64", "entry_utf8_base64", "failure_code", "failure_exception_utf8_base64",
                        "image_mvid", "runtime_framework", "runtime_version", "os_description", "os_architecture",
                        "process_architecture", "testhost_process", "managed_core_library_path", "scribe_host_path",
                        "roslyn_compiler", "roslyn_compiler_path", "sdk_compiler", "load_context_collectible",
                        "load_context_name", "loaded_assembly", "loaded_assembly_mvid", "loaded_context_name", "reference_count",
                    };
                    Require(requiredFields.All(frame.Fields.ContainsKey), "missing diagnostic context");
                    foreach (var key in new[] { "source_utf8_base64", "entry_utf8_base64", "failure_exception_utf8_base64" })
                        Require(Convert.FromBase64String(frame.Fields[key]).Length > 0, "empty diagnostic field");
                    for (var index = 0; index < Number(frame.Fields["reference_count"]); index++)
                        Require(new[] { "display", "identity", "mvid" }.All(suffix => frame.Fields.ContainsKey($"reference_{index}_{suffix}")),
                            "incomplete reference context");
                    frame.Image = frame.Chunks.SelectMany(item => item.Bytes).ToArray();
                    Require(frame.Fields.TryGetValue("image_length", out var length)
                        && Number(length) == frame.Image.Length && frame.Image.Length > 0, "image length mismatch");
                    Require(frame.Fields.GetValueOrDefault("image_sha256") == Convert.ToHexStringLower(SHA256.HashData(frame.Image)),
                        "image digest mismatch");
                    Require(frame.Chunks.Select((item, index) => item.Bytes.Length == Math.Min(3072, frame.Image.Length - index * 3072)).All(value => value),
                        "invalid chunk lengths");
                    active.Remove(id);
                    complete.Add(frame);
                    break;
                default: throw new FormatException("unknown diagnostic kind");
            }
        }
        Require(active.Count == 0 && complete.Count > 0, "missing complete frame boundaries");
        return complete;
    }

    private static DiagnosticChunk ParseChunk(string payload)
    {
        var fields = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var field in payload.Split(' '))
        {
            var parts = field.Split('=', 2);
            Require(parts.Length == 2 && fields.TryAdd(parts[0], parts[1]), "invalid chunk field");
        }
        Require(fields.Count == 4 && new[] { "index", "offset", "length", "base64" }.All(fields.ContainsKey), "missing chunk fields");
        var bytes = Convert.FromBase64String(fields["base64"]);
        Require(Number(fields["length"]) == bytes.Length && bytes.Length > 0, "chunk length mismatch");
        return new(Number(fields["index"]), Number(fields["offset"]), bytes);
    }

    private static int Number(string value) => int.TryParse(value, NumberStyles.None, CultureInfo.InvariantCulture, out var number)
        ? number : throw new FormatException("invalid nonnegative integer");

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new FormatException(message);
    }

    private sealed record DiagnosticChunk(int Index, int Offset, byte[] Bytes);

    private sealed class DiagnosticFrame
    {
        internal Dictionary<string, string> Fields { get; } = new(StringComparer.Ordinal);
        internal List<DiagnosticChunk> Chunks { get; } = [];
        internal byte[] Image { get; set; } = [];
    }

    private sealed class OverlappingWriter(Barrier overlap) : TextWriter
    {
        private readonly StringBuilder text = new();
        public override Encoding Encoding => Encoding.UTF8;
        public override void WriteLine(string? value)
        {
            lock (text) text.AppendLine(value);
            if (value?.StartsWith(DiagnosticPrefix + "BEGIN ", StringComparison.Ordinal) == true
                && !overlap.SignalAndWait(TimeSpan.FromSeconds(30)))
                throw new TimeoutException("the second failing load did not reach its diagnostic");
        }
        public override string ToString() { lock (text) return text.ToString(); }
    }

    private sealed class FailOnceWriter : StringWriter
    {
        private bool failed;
        public override void WriteLine(string? value)
        {
            if (!failed && value?.StartsWith(DiagnosticPrefix + "CHUNK ", StringComparison.Ordinal) == true)
            {
                failed = true;
                throw new IOException("diagnostic sink failure");
            }
            base.WriteLine(value);
        }
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

}
