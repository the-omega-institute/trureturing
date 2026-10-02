using System.Reflection;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

[Collection("Lean report environment")]
public sealed class ContentCheckCommandTests
{
    private const string SourcePath = "D5/S0/Synthetic/CurrentMarkdown.lean";
    private const string MarkdownPath = "Blueprint/D5/S0/Synthetic/CurrentMarkdown.md";
    private static readonly Assembly Documents = new FixtureAssembly();

    [Theory]
    [InlineData("green", false, 0, "markdown: judged=1")]
    [InlineData("green", true, 0, "markdown: judged=1")]
    [InlineData("projections", false, 1, "pinned statement projection is missing")]
    [InlineData("projections", true, 1, "pinned statement projection is missing")]
    [InlineData("describe", false, 1, "linear-formula-token")]
    [InlineData("describe", true, 1, "linear-formula-token")]
    [InlineData("markdown", false, 1, "Double subscript")]
    [InlineData("markdown", true, 1, "Double subscript")]
    [InlineData("empty-scope", true, 0, "markdown: judged=0")]
    [InlineData("missing-paths", true, 2, "paths.txt")]
    public void MatchesIndividualChecksAndStopsAtTheFirstFailure(
        string mutation, bool scoped, int expectedExit, string diagnostic)
    {
        using var fixture = new Fixture(mutation);
        var options = scoped ? new[] { "--paths-from", fixture.PathsFile } : [];
        var individual = Capture((output, error) => RunIndividual(fixture, options, output, error));
        var combined = Capture((output, error) => ScribeCli.Run(Documents,
            ["content-check", "--report", fixture.ReportPath, .. options], fixture.Root.Path, output, error));

        Assert.Equal(expectedExit, individual.Exit);
        Assert.Contains(diagnostic, individual.Output + individual.Error, StringComparison.Ordinal);
        AssertEquivalent(individual, combined);
        if (mutation is "projections" or "describe")
            Assert.DoesNotContain("markdown:", combined.Output, StringComparison.Ordinal);
        if (mutation == "projections") Assert.Empty(combined.Output);
    }

    [Theory]
    [InlineData("missing-report")]
    [InlineData("report-directory")]
    [InlineData("invalid-json")]
    [InlineData("noncanonical-json")]
    [InlineData("wrong-schema")]
    [InlineData("stale-source")]
    public void PreservesReportValidationAndItsFirstCommandDiagnostic(string mutation)
    {
        using var fixture = new Fixture(mutation);
        var individual = Capture((output, error) => RunIndividual(fixture, [], output, error));
        var combined = Capture((output, error) => ScribeCli.Run(Documents,
            ["content-check", "--report", fixture.ReportPath], fixture.Root.Path, output, error));

        Assert.Equal(2, individual.Exit);
        Assert.NotEmpty(individual.Error);
        Assert.Empty(individual.Output);
        AssertEquivalent(individual, combined);
    }

    [Theory]
    [InlineData("content-check")]
    [InlineData("content-check", "--report")]
    [InlineData("content-check", "--report", "")]
    [InlineData("content-check", "--report", "report.json", "--paths-from")]
    [InlineData("content-check", "--report", "report.json", "--paths-from", " ")]
    [InlineData("content-check", "--report", "report.json", "--bad", "paths.txt")]
    [InlineData("content-check", "--paths-from", "paths.txt", "--report", "report.json")]
    [InlineData("content-check", "--report", "report.json", "extra")]
    public void RejectsBadArgumentsBeforeResolvingARepository(params string[] arguments)
    {
        using var root = new TemporaryRoot();
        var usage = Capture((output, error) => ScribeCli.Run(Documents, ["projections"], root.Path, output, error));
        var combined = Capture((output, error) => ScribeCli.Run(Documents, arguments, root.Path, output, error));

        Assert.Equal(2, combined.Exit);
        Assert.Contains("content-check --report <file> [--paths-from <file|->]", combined.Error, StringComparison.Ordinal);
        AssertEquivalent(usage, combined);
    }

    [Fact]
    public void PreservesTheDiagnosticWhenTheReportCannotBeOpened()
    {
        using var fixture = new Fixture("green");
        using var locked = new FileStream(fixture.ReportPath, FileMode.Open, FileAccess.Read, FileShare.None);
        var individual = Capture((output, error) => RunIndividual(fixture, [], output, error));
        var combined = Capture((output, error) => ScribeCli.Run(Documents,
            ["content-check", "--report", fixture.ReportPath], fixture.Root.Path, output, error));
        Assert.Equal(2, individual.Exit);
        Assert.NotEmpty(individual.Error);
        Assert.Empty(individual.Output);
        AssertEquivalent(individual, combined);
    }

    [Fact]
    public void LoadsTheExplicitReportOnceDespiteADifferentAmbientReport()
    {
        using var fixture = new Fixture("green");
        Environment.SetEnvironmentVariable("STRATALINT_LEAN_REPORT", fixture.Root.Resolve("unavailable.json"));
        var previous = RawLeanReportArtifact.Reading.Value;
        var loads = 0;
        RawLeanReportArtifact.Reading.Value = () => loads++;
        try
        {
            var result = Capture((output, error) => ScribeCli.Run(Documents,
                ["content-check", "--report", fixture.ReportPath], fixture.Root.Path, output, error));
            Assert.True(result.Exit == 0, result.Error);
            Assert.Contains("markdown: judged=1", result.Output, StringComparison.Ordinal);
            Assert.Equal(1, loads);
        }
        finally { RawLeanReportArtifact.Reading.Value = previous; }
    }

    [Fact]
    public void PassesStandardInputScopeToMarkdownOnly()
    {
        using var fixture = new Fixture("markdown");
        var individual = Capture((output, error) => RunIndividual(fixture, ["--paths-from", "-"], output, error));
        var combined = Capture((output, error) => ScribeCli.Run(Documents,
            ["content-check", "--report", fixture.ReportPath, "--paths-from", "-"],
            fixture.Root.Path, output, error, TextReader.Null));
        Assert.Equal(0, individual.Exit);
        Assert.Contains("markdown: judged=0", individual.Output, StringComparison.Ordinal);
        AssertEquivalent(individual, combined);
    }

    private static int RunIndividual(Fixture fixture, string[] options, TextWriter output, TextWriter error)
    {
        string[][] commands =
        [
            ["projections", "--check", "--report", fixture.ReportPath],
            ["describe-report", "--check"],
            ["markdown-check", "--report", fixture.ReportPath, .. options],
        ];
        foreach (var command in commands)
        {
            var exit = ScribeCli.Run(Documents, command, fixture.Root.Path, output, error, TextReader.Null);
            if (exit != 0) return exit;
        }
        return 0;
    }

    private sealed record Transcript(int Exit, string Output, string Error, string[] Writes);

    private static Transcript Capture(Func<TextWriter, TextWriter, int> run)
    {
        var writes = new List<string>();
        using var output = new RecordingWriter("out", writes);
        using var error = new RecordingWriter("err", writes);
        var exit = run(output, error);
        return new(exit, output.ToString(), error.ToString(), writes.ToArray());
    }

    private static void AssertEquivalent(Transcript expected, Transcript actual)
    {
        Assert.Equal(expected.Exit, actual.Exit);
        Assert.Equal(expected.Output, actual.Output);
        Assert.Equal(expected.Error, actual.Error);
        Assert.Equal(expected.Writes, actual.Writes);
    }

    private sealed class RecordingWriter(string stream, List<string> writes) : TextWriter
    {
        private readonly StringBuilder text = new();
        public override Encoding Encoding => Encoding.UTF8;
        public override void Write(char value) { text.Append(value); writes.Add(stream + value); }
        public override string ToString() => text.ToString();
    }

    private sealed class Fixture : IDisposable
    {
        private readonly string? previousReport = Environment.GetEnvironmentVariable("STRATALINT_LEAN_REPORT");
        internal TemporaryRoot Root { get; } = new();
        internal string ReportPath => Root.Resolve("report.json");
        internal string PathsFile => Root.Resolve("paths.txt");

        internal Fixture(string mutation)
        {
            var definition = MarkdownCurrentCommandTests.Definition();
            SyntheticScribeRepository.WriteInputs(Root.Path, definition);
            Write("global.json", "{}\n");
            Write(definition.SourcePath, "namespace StrataLint.Scribe.Blueprint.D5.S0.Synthetic;\n");
            Write(SourcePath, "namespace D5.S0.Synthetic.CurrentMarkdown\n");
            foreach (var group in new[] { "pilot", "expansion" })
                Write($"Golden/Projection/statement-projection-{group}-v1.json",
                    $$"""{"schema":"statement-projection-{{group}}-fixture-v1","declarations":[]}""");
            Write(".gitignore", "report.json*\npaths.txt\n");
            TemporaryFileSystem.Directory.CreateDirectory(Root.Resolve(".git/objects/"));
            TemporaryFileSystem.Directory.CreateDirectory(Root.Resolve(".git/refs/heads/"));
            Write(".git/HEAD", "ref: refs/heads/fixture\n");
            Write(".git/config", "[core]\nrepositoryformatversion = 0\nbare = false\n");
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
                SnapshotDecoder.Decode(GitRepositorySnapshotReader.ReadCurrent(Root.Path))).Snapshot;
            RawLeanReportArtifact.WriteFile(ReportPath, snapshot, LeanAxiomReport.Create(
                new Dictionary<string, LeanFileReport> { [SourcePath] = new([], []) }));
            Write("paths.txt", MarkdownPath + "\0");
            Environment.SetEnvironmentVariable("STRATALINT_LEAN_REPORT", ReportPath);
            switch (mutation)
            {
                case "projections":
                    Write("Golden/Projection/statement-projection-pilot-v1.json", """
                        {"schema":"statement-projection-pilot-fixture-v1","declarations":[
                        {"name":"D5.S0.Synthetic.CurrentMarkdown.missing","source_path":"D5/S0/Synthetic/CurrentMarkdown.lean",
                         "kind":"theorem","type":"statement-v1(uparams=[],type=es(l0))"}]}
                        """);
                    goto case "markdown";
                case "describe": Write(definition.SourcePath,
                    "namespace StrataLint.Scribe.Blueprint.D5.S0.Synthetic;\n// FormulaToken\n");
                    goto case "markdown";
                case "markdown": Write(MarkdownPath, "# Probe\n\n$$u_{n}_{i}$$\n"); break;
                case "empty-scope": Write("paths.txt", ""); goto case "markdown";
                case "missing-paths": TemporaryFileSystem.File.Delete(PathsFile); break;
                case "missing-report": TemporaryFileSystem.File.Delete(ReportPath); break;
                case "report-directory":
                    TemporaryFileSystem.File.Delete(ReportPath);
                    TemporaryFileSystem.Directory.CreateDirectory(ReportPath); break;
                case "invalid-json": Write("report.json", "{"); break;
                case "noncanonical-json": Write("report.json", "{ \"modules\": [], \"schema\": \"stratalint-raw-lean-report-v2\" }\n"); break;
                case "wrong-schema": Write("report.json", "{\"modules\":[],\"schema\":\"invalid\"}\n"); break;
                case "stale-source": Write(SourcePath, "namespace Changed\n"); break;
            }
        }

        private void Write(string path, string content) => TemporaryFileSystem.File.WriteAllText(Root.Resolve(path), content);
        public void Dispose()
        {
            Environment.SetEnvironmentVariable("STRATALINT_LEAN_REPORT", previousReport);
            Root.Dispose();
        }
    }

    private sealed class FixtureAssembly : Assembly
    {
        public override Type[] GetTypes() => [typeof(ContentDocument)];
    }

    private sealed class ContentDocument : IScribeDocumentDefinition
    {
        public DocumentDefinition Create() => MarkdownCurrentCommandTests.Definition();
    }
}
