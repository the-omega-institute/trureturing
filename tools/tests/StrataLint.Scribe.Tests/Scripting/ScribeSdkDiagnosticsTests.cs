using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeSdkDiagnosticsTests
{
    private const string Entry = "Blueprint/D5/S0/Test/Probe.scribe.cs";

    [Fact]
    public void UnusedPrivateMethodReportsIDE0051BeforeExecution() =>
        Reject("private static int UnusedOrdinaryHelper() => 1;", "IDE0051");

    [Fact]
    public void UnusedPrivateFieldReportsCA1823BeforeExecution() =>
        Reject("private int unused;", "CA1823");

    [Fact]
    public void NullableReturnReportsCS8603BeforeExecution() =>
        Reject("public string NullableProbe() => null;", "CS8603");

    [Fact]
    public void CultureBannedSymbolsReportRS0030() =>
        Reject("public int BannedProbe() => int.Parse(\"1\");", "RS0030");

    [Fact]
    public void DeterminismBannedSymbolsReportRS0030() =>
        Reject("public DateTime BannedProbe() => DateTime.UtcNow;", "RS0030");

    [Fact]
    public void GuidBannedSymbolsReportRS0030() =>
        Reject("public Guid BannedProbe() => Guid.NewGuid();", "RS0030");

    [Fact]
    public void SelectedDefinitionCannotReferenceAnotherDefinition()
    {
        using var root = Root();
        Write(root, Entry, Definition("public int FromOtherDefinition() => Other.Value;"));
        Write(root, "Blueprint/D5/S0/Test/Other.scribe.cs",
            "internal static class Other { public static int Value => 1; }");
        var (exit, _, error) = Verify(root, Entry);
        Assert.Equal(1, exit);
        Assert.Contains("CS0103", error, StringComparison.Ordinal);
        Assert.Contains(Entry, error, StringComparison.Ordinal);
    }

    [Fact]
    public void LegalDefinitionPassesSdkAndExecutes()
    {
        using var root = Root();
        Write(root, Entry, Definition(""));
        var (exit, output, error) = Verify(root, Entry);
        Assert.Equal(0, exit);
        Assert.Contains("paths=1 hostFailures=0", output, StringComparison.Ordinal);
        Assert.Empty(error);
    }

    [Fact]
    public void WrittenLocalPragmaReasonAllowsUnusedPrivateMethod()
    {
        using var root = Root();
        Write(root, Entry, Definition("""
            // The private helper is reserved for the reflection consumer of this fixture.
            #pragma warning disable IDE0051
            private static int ReflectionHelper() => 1;
            #pragma warning restore IDE0051
            """));
        var result = Verify(root, Entry);
        Assert.True(result.Exit == 0, result.Error);
    }

    [Fact]
    public void UnselectedInvalidDefinitionDoesNotAffectSelectedResult()
    {
        using var root = Root();
        Write(root, Entry, Definition(""));
        Write(root, "Blueprint/D5/S0/Test/Other.scribe.cs", "this is invalid C#");
        var (exit, _, error) = Verify(root, Entry);
        Assert.Equal(0, exit);
        Assert.Empty(error);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EmitAndCheckRejectSdkDiagnosticBeforeReadingLeanReport(bool check)
    {
        using var root = Root();
        Write(root, Entry, Definition("private static int Unused() => 1;"));
        var error = new StringWriter();
        var exit = ScribeEmitter.EmitPaths(root.Path, [Entry], check, TextWriter.Null, error,
            () => throw new InvalidOperationException("LeanReportWasRead"));
        Assert.Equal(1, exit);
        Assert.Contains("IDE0051", error.ToString(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ContentAndMarkdownRejectSdkDiagnosticBeforeExecution(bool content)
    {
        using var root = Root();
        Write(root, Entry, Definition("private static int Unused() => 1;"));
        var error = new StringWriter();
        var exit = ScribeContentChecks.Run(root.Path, [Entry], EmptyReport(), content, TextWriter.Null, error);
        Assert.Equal(1, exit);
        Assert.Contains("IDE0051", error.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void EmptySelectionDoesNotStartOrRequireSdk()
    {
        using var root = new TemporaryRoot();
        var result = ScribeSdkAdmission.Check(root.Path, [], dotnetPath: "missing-dotnet");
        Assert.Equal(0, result.ExitCode);
        Assert.Empty(result.Paths);
        Assert.False(Directory.Exists(root.Resolve("build/scribe-sdk")));
    }

    [Fact]
    public void MissingSdkIsInfrastructureFailureWithoutExecutionFallback()
    {
        using var root = Root();
        Write(root, Entry, Definition(""));
        var result = ScribeSdkAdmission.Check(root.Path, [Entry], root.Resolve("missing-dotnet"));
        Assert.Equal(2, result.ExitCode);
        Assert.NotNull(result.InfrastructureFailure);
        Assert.Empty(result.Diagnostics);
    }

    [Fact]
    public void FailedSdkInvocationIsInfrastructureFailure()
    {
        using var root = Root();
        Write(root, Entry, Definition(""));
        Write(root, "global.json", "{invalid json}");
        var result = ScribeSdkAdmission.Check(root.Path, [Entry]);
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("SDK invocation", result.InfrastructureFailure, StringComparison.Ordinal);
    }

    [Fact]
    public void ProjectCompileInputIsExactlySelectedDefinition()
    {
        using var root = Root();
        Write(root, Entry, Definition(""));
        Write(root, "Blueprint/D5/S0/Test/Unselected.scribe.cs", "invalid source");
        using var batch = ScribeSdkBatch.Create(root.Path, [Entry]);
        var parent = Path.GetDirectoryName(batch.ProjectPath)!;
        var project = System.Xml.Linq.XDocument.Load(Assert.Single(Directory.GetFiles(parent, "*.csproj", SearchOption.AllDirectories)));
        Assert.Equal("false", project.Descendants("EnableDefaultCompileItems").Single().Value);
        Assert.Equal(new[] { Entry },
            project.Descendants("Compile").Select(item => Path.GetRelativePath(root.Path, item.Attribute("Include")!.Value).Replace('\\', '/')).Order(StringComparer.Ordinal));
        Assert.Empty(project.Descendants("ProjectReference"));
        var dispatch = System.Xml.Linq.XDocument.Load(batch.ProjectPath);
        Assert.All(dispatch.Descendants("MSBuild"), task =>
            Assert.Equal("Configuration=Release", task.Attribute("Properties")?.Value));
        Assert.Equal(new[]
        {
            "Dunet.Generator.dll", "Dunet.dll", "Microsoft.CodeAnalysis.Analyzers.dll",
            "Microsoft.CodeAnalysis.CSharp.Analyzers.dll", "Microsoft.CodeAnalysis.BannedApiAnalyzers.dll",
            "Microsoft.CodeAnalysis.CSharp.BannedApiAnalyzers.dll", "Tomlyn.SourceGeneration.dll",
        }.Order(StringComparer.Ordinal), project.Descendants("Analyzer")
            .Select(item => Path.GetFileName(item.Attribute("Include")!.Value)).Order(StringComparer.Ordinal));
    }

    [Fact]
    public void SdkAdmissionHandlesSpacesInCandidateRoot()
    {
        using var temporary = new TemporaryRoot();
        var root = temporary.Resolve("candidate with spaces");
        StrataLint.TestSupport.ScribeSdkFixtureInputs.Write(root);
        var source = Path.Combine(root, Entry);
        Directory.CreateDirectory(Path.GetDirectoryName(source)!);
        File.WriteAllText(source, Definition(""));
        var result = ScribeSdkAdmission.Check(root, [Entry]);
        Assert.True(result.ExitCode == 0, result.InfrastructureFailure ?? string.Join("\n", result.Diagnostics));
    }

    [Fact]
    public void DefinitionDirectoryEditorConfigAppliesToOriginalSourcePath()
    {
        using var root = Root();
        Write(root, Entry, Definition("private static int Unused() => 1;"));
        Write(root, "Blueprint/D5/S0/Test/.editorconfig", "[*.cs]\ndotnet_diagnostic.IDE0051.severity = none\n");
        var result = ScribeSdkAdmission.Check(root.Path, [Entry]);
        Assert.True(result.ExitCode == 0, result.InfrastructureFailure ?? string.Join("\n", result.Diagnostics));
    }

    private static void Reject(string member, string id)
    {
        using var root = Root();
        Write(root, Entry, Definition(member));
        const string other = "Blueprint/D5/S0/Test/Other.scribe.cs";
        Write(root, other, """
            using StrataLint.Scribe;
            internal sealed class Other : IScribeDocumentDefinition
            { public DocumentDefinition Create() => null!; }
            """);
        var (exit, _, error) = Verify(root, Entry + "\n" + other);
        Assert.Equal(1, exit);
        Assert.Contains(id, error, StringComparison.Ordinal);
        Assert.Contains(Entry, error, StringComparison.Ordinal);
        Assert.DoesNotContain("CreateFailed", error, StringComparison.Ordinal);
    }

    internal static TemporaryRoot Root()
    {
        var root = new TemporaryRoot();
        WriteConfiguration(root);
        return root;
    }

    internal static void WriteConfiguration(TemporaryRoot root) =>
        StrataLint.TestSupport.ScribeSdkFixtureInputs.Write(root.Path);

    private static void Write(TemporaryRoot root, string path, string text) => File.WriteAllText(root.Resolve(path), text);

    private static (int Exit, string Output, string Error) Verify(TemporaryRoot root, string paths)
    {
        var output = new StringWriter();
        var error = new StringWriter();
        var exit = ScribeCli.Run(["scripts", "verify", "--paths-from", "-"], root.Path,
            output, error, new StringReader(paths));
        return (exit, output.ToString(), error.ToString());
    }

    private static LeanAxiomReport EmptyReport() => LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>());

    private static string Definition(string member) => $$"""
        using StrataLint.Scribe;
        using static StrataLint.Scribe.DefinitionDsl;
        internal sealed class Probe : IScribeDocumentDefinition
        {
            {{member}}
            public DocumentDefinition Create() => DocumentDefinition.Create(
                ScribeNode.Create("digest", H("Probe"), Blocks(Paragraph(Text("body")))));
        }
        """;
}
