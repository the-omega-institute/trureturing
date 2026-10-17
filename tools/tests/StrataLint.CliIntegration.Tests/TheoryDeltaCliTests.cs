using System.Text;
using System.Text.Json;
using System.Security.Cryptography;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.EngineeringScope;

namespace StrataLint.CliIntegration.Tests;

public sealed class TheoryDeltaCliTests
{
    private const string Document = "docs/develop/theory/Fixture.MD";

    [Theory]
    [InlineData(5000, 0)]
    [InlineData(5001, 1)]
    public void TheoryDeltaUsesCapacityOwnerWithoutReport(int lines, int exitCode)
    {
        var fixture = new RuleFixture();
        fixture.Files[Document] = string.Concat(Enumerable.Repeat("line\n", lines));
        var result = Check(fixture, RawChangeSet.Create([Document]));

        Assert.Equal(exitCode, result.ExitCode);
        Assert.Empty(result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal(["SL-003", "SL-015"], json.RootElement.GetProperty("executed")
            .EnumerateArray().Select(static value => value.GetString()!).ToArray());
        if (exitCode != 0) Assert.Contains("5001 lines (hard limit 5000)", result.Output);
    }

    [Theory]
    [InlineData("modified")]
    [InlineData("deleted")]
    public void TheoryDeltaPreservesModificationAndDeletionSemantics(string kind)
    {
        var fixture = new RuleFixture();
        fixture.Baseline[Document] = new string('\n', 6000);
        if (kind == "modified") fixture.Files[Document] = new string('\n', 5001);
        var changes = RawChangeSet.CreateWithKinds([(Document, kind == "deleted"
            ? RawChangeKind.Deleted : RawChangeKind.Modified)]);

        Assert.Equal(kind == "deleted" ? 0 : 1, Check(fixture, changes).ExitCode);
    }

    [Theory]
    [InlineData("README.md")]
    [InlineData("D5/S0/Carrier/Ring.lean")]
    [InlineData("docs/develop/theory-other/Foo.md")]
    public void ReportFreeDeltaRejectsMixedOrMovedOutChanges(string other)
    {
        var fixture = new RuleFixture();
        fixture.Files[Document] = "theory\n";
        var result = Check(fixture, RawChangeSet.Create([Document, other]));
        Assert.Equal(2, result.ExitCode);
        Assert.NotEmpty(result.Error);
    }

    [Fact]
    public void ReportFreeDeltaRejectsEmptySelectionAndCaseCollisions()
    {
        var fixture = new RuleFixture();
        Assert.Equal(2, Check(fixture, RawChangeSet.Create(Array.Empty<string>())).ExitCode);
        fixture.Files[Document] = "theory\n";
        fixture.Files["docs/develop/theory/fixture.md"] = "duplicate\n";
        var result = Check(fixture, RawChangeSet.Create([Document]));
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("case-colliding", result.Error);
    }

    [Fact]
    public void ReportFreeDeltaRetainsFileMapMembership()
    {
        var fixture = new RuleFixture();
        fixture.Files[Document] = "theory\n";
        fixture.Files["Meta/FILEMAP.toml"] = fixture.Files["Meta/FILEMAP.toml"].Replace(
            "docs/develop/theory/**", "docs/develop/other/**", StringComparison.Ordinal);
        var result = Check(fixture, RawChangeSet.Create([Document]));
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("FILEMAP", result.Error);
    }

    [Fact]
    public void ProductionGatewayChecksWholeBeforeRangeWithoutLakeAndRejectsUndeclaredLink()
    {
        using var directory = new TemporaryDirectory();
        var root = Path.Combine(directory.Path, "theory delta with spaces");
        Directory.CreateDirectory(root);
        var fixture = new RuleFixture();
        foreach (var (path, text) in fixture.Files)
        {
            var destination = Path.Combine(root, path);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.WriteAllText(destination, text);
        }
        string Git(params string[] args)
        {
            var result = TestProcessRunner.Run("git", args, root, TestBudgets.ScriptProcessHangGuard, 64 * 1024);
            Assert.Equal(0, result.ExitCode);
            return Encoding.UTF8.GetString(result.StandardOutput).Trim();
        }
        Git("init", "-q");
        Git("add", ".");
        Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "base");
        var before = Git("rev-parse", "HEAD");
        var document = Path.Combine(root, Document);
        Directory.CreateDirectory(Path.GetDirectoryName(document)!);
        File.WriteAllText(document, new string('\n', 5000));
        Git("add", ".");
        Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "theory");
        var result = Run();
        Assert.Equal(0, result.ExitCode);
        Assert.False(Directory.Exists(Path.Combine(root, ".lake")));
        File.WriteAllText(document, new string('\n', 5001));
        Assert.Equal(1, Run().ExitCode);
        File.Delete(document);
        File.CreateSymbolicLink(document, "../../../README.md");
        Assert.Equal(2, Run().ExitCode);

        StrataLint.Runtime.ProcessOutput Run() => TestProcessRunner.Run("dotnet",
            [typeof(StrataLint.Cli.Program).Assembly.Location, "check-delta", "--protected-base", before],
            root, TestBudgets.ScriptProcessHangGuard, 64 * 1024);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ProductionTheoryDeltaIgnoresCopyProvenanceButChecksRealEndpoints(bool opaqueSource)
    {
        using var directory = new TemporaryDirectory();
        const string sourceText = @"| $u$ | $\beta$ | $\bot$ | $\mathrm{br}$ | $\mathrm{br}$ | $\beta$";
        var sourcePath = opaqueSource
            ? "Meta/Digestion/atoms/sha256/" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(sourceText)))
            : "README.md";
        var fixture = new RuleFixture();
        fixture.Files[sourcePath] = sourceText;
        foreach (var (path, text) in fixture.Files)
        {
            var destination = Path.Combine(directory.Path, path);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.WriteAllText(destination, text);
        }
        string Git(params string[] args)
        {
            var result = TestProcessRunner.Run("git", args, directory.Path, TestBudgets.ScriptProcessHangGuard, 64 * 1024);
            Assert.Equal(0, result.ExitCode);
            return Encoding.UTF8.GetString(result.StandardOutput).Trim();
        }
        Git("init", "-q");
        Git("add", ".");
        Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "base");
        var before = Git("rev-parse", "HEAD");
        var document = Path.Combine(directory.Path, Document);
        Directory.CreateDirectory(Path.GetDirectoryName(document)!);
        const string theory = "# Generic source admission probe\n\n## Claim 1\n\n"
            + "A canonical regular generic theory input remains eligible.\n";
        File.WriteAllText(document, theory);
        Git("add", ".");
        Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "theory");

        var changes = new GitRepositoryGateway(directory.Path).Prepare(before).Changes;
        Assert.Contains(changes.Entries, change => change.Path.Value == sourcePath && change.Kind == RawChangeKind.Copied);
        Assert.Contains(changes.Entries, change => change.Path.Value == Document && change.Kind == RawChangeKind.Added);
        var accepted = Run();
        Assert.Equal(0, accepted.ExitCode);
        Assert.Empty(accepted.StandardError);
        using var output = JsonDocument.Parse(accepted.StandardOutput);
        Assert.Equal(["SL-003", "SL-015"], output.RootElement.GetProperty("executed")
            .EnumerateArray().Select(static value => value.GetString()!).ToArray());
        Assert.Equal(sourceText, File.ReadAllText(Path.Combine(directory.Path, sourcePath)));
        Assert.False(Directory.Exists(Path.Combine(directory.Path, ".lake")));

        File.WriteAllText(document, new string('\n', 5001));
        var oversized = Run();
        Assert.Equal(1, oversized.ExitCode);
        Assert.Contains("5001 lines (hard limit 5000)", Encoding.UTF8.GetString(oversized.StandardOutput));
        File.WriteAllText(document, theory);
        var source = Path.Combine(directory.Path, sourcePath);
        File.WriteAllText(source, sourceText + "\nchanged\n");
        var modified = Run();
        Assert.Equal(2, modified.ExitCode);
        Assert.Contains("other changes require --candidate-lean-report", Encoding.UTF8.GetString(modified.StandardError));
        File.Delete(source);
        var deleted = Run();
        Assert.Equal(2, deleted.ExitCode);
        Assert.Contains("other changes require --candidate-lean-report", Encoding.UTF8.GetString(deleted.StandardError));

        StrataLint.Runtime.ProcessOutput Run() => TestProcessRunner.Run("dotnet",
            [typeof(StrataLint.Cli.Program).Assembly.Location, "check-delta", "--protected-base", before],
            directory.Path, TestBudgets.ScriptProcessHangGuard, 64 * 1024);
    }

    [Fact]
    public void ReportFreeDeltaRejectsCopyProvenanceWithoutAChangedEndpoint()
    {
        var fixture = new RuleFixture();
        var changes = RawChangeSet.CreateWithKinds([(RuleFixture.FixtureCasPath, RawChangeKind.Copied)]);
        var result = Check(fixture, changes);
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("nonempty theory-only change", result.Error);
    }

    private static ExplicitCommandResult Check(RuleFixture fixture, RawChangeSet changes)
    {
        static RawRepositorySnapshot Snapshot(Dictionary<string, string> files) =>
            RawRepositorySnapshot.Create(files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var gateway = new FakeRepositoryGateway(changes, Snapshot(fixture.Files), Snapshot(fixture.Baseline));
        var environment = new ProductionCliEnvironment("/fixture", gateway, new FakeLeanReportSource(null));
        return environment.CheckDelta(["--protected-base", new string('a', 40)]);
    }
}
