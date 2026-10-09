using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class ContentCheckCommandTests
{
    [Theory]
    [InlineData("content-check", "--report", "report.json")]
    [InlineData("emit")]
    [InlineData("emit", "--check")]
    public void MissingManifestFailsBeforeRepositoryResolution(params string[] arguments)
    {
        using var root = new TemporaryRoot(sdkConfiguration: true);
        var error = new StringWriter();
        Assert.Equal(2, ScribeCli.Run(arguments, root.Path, TextWriter.Null, error));
        Assert.Contains("MissingPathsManifest", error.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void MissingContentManifestFailsWithAValidRepositoryAndReport()
    {
        using var fixture = new Fixture();
        var error = new StringWriter();
        Assert.Equal(2, ScribeCli.Run(["content-check", "--report", "fixture.json"],
            fixture.Root.Path, TextWriter.Null, error, fixture.Report));
        Assert.Contains("MissingPathsManifest", error.ToString(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("content-check")]
    [InlineData("content-check", "--report")]
    [InlineData("content-check", "--report", "report.json", "--paths-from")]
    [InlineData("content-check", "--report", "report.json", "--bad", "paths.txt")]
    [InlineData("content-check", "--paths-from", "paths.txt", "--report", "report.json")]
    [InlineData("content-check", "--report", "report.json", "extra")]
    [InlineData("content-check", "--report", "", "--paths-from", "paths.txt")]
    [InlineData("content-check", "--report", "report.json", "--paths-from", " ")]
    public void RejectsBadArgumentsBeforeResolvingARepository(params string[] arguments)
    {
        using var root = new TemporaryRoot(sdkConfiguration: true);
        var error = new StringWriter();
        Assert.Equal(2, ScribeCli.Run(arguments, root.Path, TextWriter.Null, error));
        Assert.Contains("usage:", error.ToString(), StringComparison.Ordinal);
        Assert.DoesNotContain("Repository", error.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void ChecksOnlySelectedDefinitionAndDoesNotExecuteUnselectedDefinitions()
    {
        using var fixture = new Fixture();
        fixture.Write("Blueprint/D5/S0/Synthetic/Unselected.scribe.cs", "invalid C# // FormulaToken");
        fixture.Write("Blueprint/D5/S0/Synthetic/Unselected.md", "$$u_{n}_{i}$$");
        var output = new StringWriter();
        var error = new StringWriter();
        var exit = fixture.Run(Path, output, error);
        Assert.True(exit == 0, error.ToString());
        Assert.Contains("content-check: definitions=1", output.ToString(), StringComparison.Ordinal);
        Assert.Contains("markdown: judged=1", output.ToString(), StringComparison.Ordinal);
        Assert.Equal(1, fixture.Run("Blueprint/D5/S0/Synthetic/Unselected.scribe.cs", TextWriter.Null, new StringWriter()));
    }

    [Fact]
    public void EmptyManifestExecutesNoDefinitionsAndIgnoresUnselectedMarkdown()
    {
        using var fixture = new Fixture();
        fixture.Write(Path, "invalid C#");
        fixture.Write(Markdown, "$$u_{n}_{i}$$");
        var output = new StringWriter();
        var error = new StringWriter();
        Assert.Equal(0, fixture.Run("", output, error));
        Assert.Contains("content-check: definitions=0", output.ToString(), StringComparison.Ordinal);
        Assert.Contains("markdown: judged=0", output.ToString(), StringComparison.Ordinal);
        Assert.Empty(error.ToString());
    }

    [Fact]
    public void MarkdownOnlyPlainTextDoesNotExecuteDefinition()
    {
        using var fixture = new Fixture();
        fixture.Write(Path, UnselectedDefinition);
        fixture.Write(Markdown, "# Updated narrative\n\nOrdinary text.\n");
        var output = new StringWriter();
        var error = new StringWriter();

        Assert.True(fixture.Run(Markdown, output, error) == 0, error.ToString());
        Assert.Contains("content-check: definitions=0", output.ToString(), StringComparison.Ordinal);
        Assert.Contains("markdown: judged=1 formula(s)=0 red=0", output.ToString(), StringComparison.Ordinal);
        Assert.Empty(error.ToString());
    }

    [Fact]
    public void MarkdownOnlyInvalidFormulaIsRejectedWithoutExecutingDefinition()
    {
        using var fixture = new Fixture();
        fixture.Write(Path, UnselectedDefinition);
        fixture.Write(Markdown, "$$u_{n}_{i}$$");
        var output = new StringWriter();
        var error = new StringWriter();

        Assert.Equal(1, fixture.Run(Markdown, output, error));
        Assert.Contains("content-check: definitions=0", output.ToString(), StringComparison.Ordinal);
        Assert.Contains("markdown: judged=1 formula(s)=1 red=1", output.ToString(), StringComparison.Ordinal);
        Assert.Contains("markdown red " + Markdown, error.ToString(), StringComparison.Ordinal);
        Assert.Contains("Double subscript", error.ToString(), StringComparison.Ordinal);
        Assert.DoesNotContain("Compilation", error.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void ChecksSelectedDefinitionAndItsMarkdownFormula()
    {
        using var fixture = new Fixture();
        fixture.Write(Markdown, "$$u_{n}_{i}$$");
        var output = new StringWriter();
        var error = new StringWriter();
        Assert.Equal(1, fixture.Run(Path, output, error));
        Assert.Contains("content-check: definitions=1", output.ToString(), StringComparison.Ordinal);
        Assert.Contains("markdown: judged=1", output.ToString(), StringComparison.Ordinal);
        Assert.Contains("Double subscript", error.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void ManyMarkdownOnlyChangesExecuteNoDefinitions()
    {
        using var fixture = new Fixture();
        var paths = new List<string>();
        for (var index = 0; index < 64; index++)
        {
            var stem = $"Blueprint/D5/S0/Synthetic/Reemitted{index}";
            fixture.Write(stem + ".scribe.cs", UnselectedDefinition);
            fixture.Write(stem + ".md", $"# Reemitted {index}\n\nA formula $x^2$.\n");
            paths.Add(stem + ".md");
        }
        var output = new StringWriter();
        var error = new StringWriter();

        Assert.True(fixture.Run(string.Join('\0', paths), output, error) == 0, error.ToString());
        Assert.Contains("content-check: definitions=0", output.ToString(), StringComparison.Ordinal);
        Assert.Contains("markdown: judged=64 formula(s)=64 red=0", output.ToString(), StringComparison.Ordinal);
        Assert.Empty(error.ToString());
    }

    [Fact]
    public void SelectedSourceGovernanceIsPreserved()
    {
        using var fixture = new Fixture();
        File.AppendAllText(fixture.Root.Resolve(Path), "\n// FormulaToken\n");
        var error = new StringWriter();
        Assert.Equal(1, fixture.Run(Path, TextWriter.Null, error));
        Assert.Contains("linear-formula-token", error.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void ExplicitMarkdownWithoutDefinitionIsRejected()
    {
        using var fixture = new Fixture();
        const string orphan = "Blueprint/D5/S0/Synthetic/Orphan.md";
        fixture.Write(orphan, "# Orphan");
        var output = new StringWriter();
        var error = new StringWriter();
        Assert.Equal(1, fixture.Run(orphan, output, error));
        Assert.Contains("content-check: definitions=0", output.ToString(), StringComparison.Ordinal);
        Assert.Contains("markdown red " + orphan, error.ToString(), StringComparison.Ordinal);
        Assert.Contains("no Scribe document renders", error.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void ProjectionFailurePrecedesScriptExecution()
    {
        using var fixture = new Fixture();
        fixture.Write(Path, "invalid C#");
        fixture.Write("Golden/Projection/statement-projection-pilot-v1.json", """
            {"schema":"statement-projection-pilot-fixture-v1","declarations":[
            {"name":"D5.S0.Synthetic.CurrentMarkdown.missing","source_path":"D5/S0/Synthetic/CurrentMarkdown.lean",
             "kind":"theorem","type":"statement-v1(uparams=[],type=es(l0))"}]}
            """);
        var error = new StringWriter();
        Assert.Equal(1, fixture.Run(Path, TextWriter.Null, error));
        Assert.Contains("pinned statement projection is missing", error.ToString(), StringComparison.Ordinal);
        Assert.DoesNotContain("CompilationFailed", error.ToString(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("report-directory")]
    [InlineData("invalid-json")]
    [InlineData("noncanonical-json")]
    [InlineData("wrong-schema")]
    [InlineData("stale-source")]
    public void ExplicitReportValidationPrecedesDefinitionExecution(string mutation)
    {
        using var fixture = new Fixture();
        fixture.WriteReport();
        switch (mutation)
        {
            case "missing": File.Delete(fixture.ReportPath); break;
            case "report-directory":
                File.Delete(fixture.ReportPath);
                Directory.CreateDirectory(fixture.ReportPath);
                break;
            case "invalid-json": fixture.Write("report.json", "{"); break;
            case "noncanonical-json":
                fixture.Write("report.json", "{ \"modules\": [], \"schema\": \"stratalint-raw-lean-report-v3\" }\n");
                break;
            case "wrong-schema": fixture.Write("report.json", "{\"modules\":[],\"schema\":\"invalid\"}\n"); break;
            case "stale-source": fixture.Write("D5/S0/Synthetic/CurrentMarkdown.lean", "namespace Changed\n"); break;
        }
        fixture.Write(Path, "invalid C#");
        var error = new StringWriter();
        Assert.Equal(2, fixture.RunWithReport(error));
        Assert.NotEmpty(error.ToString());
        Assert.DoesNotContain("Compilation:", error.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void ReportCannotBeOpenedFailsBeforeDefinitionExecution()
    {
        using var fixture = new Fixture();
        fixture.WriteReport();
        fixture.Write(Path, "invalid C#");
        using var locked = new FileStream(fixture.ReportPath, FileMode.Open, FileAccess.Read, FileShare.None);
        var error = new StringWriter();
        Assert.Equal(2, fixture.RunWithReport(error));
        Assert.NotEmpty(error.ToString());
        Assert.DoesNotContain("Compilation:", error.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void ExplicitReportIsLoadedOnce()
    {
        using var fixture = new Fixture();
        fixture.WriteReport();
        var previous = RawLeanReportArtifact.Reading.Value;
        var loads = 0;
        RawLeanReportArtifact.Reading.Value = () => loads++;
        try
        {
            var error = new StringWriter();
            Assert.True(fixture.RunWithReport(error) == 0, error.ToString());
            Assert.Equal(1, loads);
        }
        finally { RawLeanReportArtifact.Reading.Value = previous; }
    }

    [Fact]
    public void DescribeReportConsumesTheExactPackWithoutExecutingDefinitions()
    {
        using var fixture = new Fixture();
        var packPath = fixture.Root.Resolve("pack.zip");
        var manifest = ScribeResourcePack.Write(packPath, [MarkdownCurrentCommandTests.Definition()]);
        fixture.Write(Path, "invalid C#");
        var output = new StringWriter();
        var error = new StringWriter();
        int Run(string digest) => ScribeCli.Run(["describe-report", "--scribe-pack", packPath,
            "--scribe-pack-digest", digest, "--json", "--check"], fixture.Root.Path, output, error,
            fixture.Report);
        Assert.True(Run(manifest.TotalSha256) == 0, error.ToString());
        Assert.Contains("scribe-describe-report-v3", output.ToString(), StringComparison.Ordinal);
        Assert.Equal(2, Run(new string('0', 64)));
        Assert.Contains("ScribePackDigestMismatch", error.ToString(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("emit")]
    [InlineData("content-check")]
    [InlineData("markdown-check")]
    [InlineData("projections")]
    [InlineData("describe-report")]
    public void CommandsLoadFileReportWithoutGit(string command)
    {
        using var fixture = new Fixture();
        fixture.WriteFileReport();
        Assert.False(Directory.Exists(fixture.Root.Resolve(".git")));
        var output = new StringWriter();
        var error = new StringWriter();
        Assert.True(fixture.RunCommand(command, output, error) == 0, error.ToString());
        Assert.Empty(error.ToString());
        if (command == "emit")
            Assert.True(File.Exists(fixture.Root.Resolve(Markdown)));
    }

    [Theory]
    [InlineData("emit")]
    [InlineData("content-check")]
    [InlineData("markdown-check")]
    [InlineData("projections")]
    [InlineData("describe-report")]
    public void CommandsRejectFileReportSourceDriftWithoutGit(string command)
    {
        using var fixture = new Fixture();
        fixture.WriteFileReport();
        fixture.Write("D5/S0/Synthetic/CurrentMarkdown.lean", "namespace Changed\n");
        var error = new StringWriter();
        Assert.Equal(2, fixture.RunCommand(command, TextWriter.Null, error));
        Assert.Contains("Raw Lean report source hash does not match D5/S0/Synthetic/CurrentMarkdown.lean",
            error.ToString(), StringComparison.Ordinal);
    }

    private const string Path = "Blueprint/D5/S0/Synthetic/CurrentMarkdown.scribe.cs";
    private const string Markdown = "Blueprint/D5/S0/Synthetic/CurrentMarkdown.md";
    private const string UnselectedDefinition = """
        using System;
        using StrataLint.Scribe;
        internal sealed class Unselected : IScribeDocumentDefinition
        {
            public DocumentDefinition Create() => throw new InvalidOperationException("definition must not execute");
        }
        """;

    private sealed class Fixture : IDisposable
    {
        internal TemporaryRoot Root { get; } = new(sdkConfiguration: true);
        internal readonly LeanAxiomReport Report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
            { ["D5/S0/Synthetic/CurrentMarkdown.lean"] = new([], []) });
        internal Fixture()
        {
            SyntheticScribeRepository.WriteInputs(Root.Path, MarkdownCurrentCommandTests.Definition());
            Write("global.json", "{}\n");
            Write("D5/S0/Synthetic/CurrentMarkdown.lean", "namespace D5.S0.Synthetic.CurrentMarkdown\n");
            Write(Path, $$"""
                using StrataLint.Scribe;
                using static StrataLint.Scribe.DefinitionDsl;
                {{"namespace StrataLint.Scribe.Blueprint.D5.S0.Synthetic;"}}
                internal sealed class CurrentMarkdown : IScribeDocumentDefinition
                {
                    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
                        Header("D5/S0/Synthetic/CurrentMarkdown", "Current Markdown command fixture."),
                        H("Current Markdown"), Blocks(Paragraph(Text("A current formula "),
                        Math(FormulaDsl.Id("x")), Text(".")))));
                }
                """);
            foreach (var group in new[] { "pilot", "expansion" })
                Write($"Golden/Projection/statement-projection-{group}-v1.json",
                    $$"""{"schema":"statement-projection-{{group}}-fixture-v1","declarations":[]}""");
        }
        internal int Run(string selection, TextWriter output, TextWriter error) => ScribeCli.Run(
            ["content-check", "--report", "fixture.json", "--paths-from", "-"],
            Root.Path, output, error, Report, new StringReader(selection));
        internal string ReportPath => Root.Resolve("report.json");
        internal void WriteReport()
        {
            Write(".gitignore", "report.json*\n");
            Directory.CreateDirectory(Root.Resolve(".git/objects"));
            Directory.CreateDirectory(Root.Resolve(".git/refs/heads"));
            Write(".git/HEAD", "ref: refs/heads/fixture\n");
            Write(".git/config", "[core]\nrepositoryformatversion = 0\nbare = false\n");
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
                GitRepositorySnapshotReader.ReadCurrent(Root.Path))).Snapshot;
            RawLeanReportArtifact.WriteFile(ReportPath, snapshot, Report);
        }
        internal void WriteFileReport()
        {
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
                RawRepositorySnapshot.Create(Directory.EnumerateFiles(Root.Path, "*.lean", SearchOption.AllDirectories)
                    .Select(path => new RawRepositoryEntry(System.IO.Path.GetRelativePath(Root.Path, path).Replace('\\', '/'),
                        System.Collections.Immutable.ImmutableArray.CreateRange(File.ReadAllBytes(path))))))).Snapshot;
            RawLeanReportArtifact.WriteFile(ReportPath, snapshot, Report);
            RawLeanReportArtifact.WriteFile(RawLeanReportArtifact.DefaultPath(Root.Path), snapshot, Report);
        }
        internal int RunCommand(string command, TextWriter output, TextWriter error)
        {
            IReadOnlyList<string> arguments;
            if (command == "describe-report")
            {
                var packPath = Root.Resolve("pack.zip");
                var manifest = ScribeResourcePack.Write(packPath, [MarkdownCurrentCommandTests.Definition()]);
                arguments = [command, "--scribe-pack", packPath, "--scribe-pack-digest", manifest.TotalSha256, "--json", "--check"];
            }
            else if (command == "projections")
                arguments = [command, "--check", "--report", ReportPath];
            else if (command == "emit")
                arguments = [command, "--paths-from", "-"];
            else
                arguments = [command, "--report", ReportPath, "--paths-from", "-"];
            return ScribeCli.Run(arguments, Root.Path, output, error, leanReport: null, new StringReader(Path));
        }
        internal int RunWithReport(TextWriter error) => ScribeCli.Run(
            ["content-check", "--report", ReportPath, "--paths-from", "-"],
            Root.Path, TextWriter.Null, error, leanReport: null, new StringReader(Path));
        internal void Write(string path, string text) => File.WriteAllText(Root.Resolve(path), text);
        public void Dispose() => Root.Dispose();
    }
}
