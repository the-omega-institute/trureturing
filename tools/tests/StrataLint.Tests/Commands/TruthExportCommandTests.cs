using System.Collections.Immutable;
using System.IO.Compression;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed class TruthExportCommandTests
{
    private const string Toolchain = "leanprover/lean4:v4.24.0\n";
    private const string Lakefile = "[package]\nname = \"fixture\"\n";
    private const string Manifest = "{}\n";

    [Fact]
    public void ExportEqualsStrictActiveFreezeSnapshot()
    {
        using var fixture = DivergentLedgerFixture();
        using var output = new TemporaryDirectory();

        var (exitCode, console) = Run(fixture, output.Path);

        Assert.Equal(0, exitCode);
        Assert.Equal(string.Empty, console.Error);
        var exportPath = Path.Combine(output.Path, "truth-export.v1.json");
        Assert.True(File.Exists(exportPath));
        using (var document = JsonDocument.Parse(
                   TemporaryFileSystem.ReadAllBytes(output, "truth-export.v1.json")))
        {
            Assert.False(document.RootElement.TryGetProperty("lean_report_digest", out _));
        }

        var model = ParseExport(output);
        Assert.Equal("TruthExportCommand", model.Producer);

        var expected = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateHistory(fixture.LedgerFiles, fixture.FinalCatalog)).Capability.ActiveFrozenNodes;

        Assert.Equal(
            expected.Select(static node => node.RepoPath.Value).Order(StringComparer.Ordinal),
            model.Nodes.Select(static node => node.RepoPath));
        Assert.DoesNotContain(model.Nodes, node => node.RepoPath == PathFor("B"));
        Assert.Contains(model.Nodes, node => node.RepoPath == PathFor("A"));
        Assert.Contains(model.Nodes, node => node.RepoPath == PathFor("C"));

        foreach (var node in expected)
        {
            var exportedNode = model.Nodes.Single(item => item.FrozenNodeId == node.FrozenNodeId.Value);
            Assert.Equal(node.RepoPath.Value, exportedNode.RepoPath);
            Assert.Equal(node.AxiomClosure, exportedNode.AxiomClosure);
            Assert.Equal(
                node.DeclarationStatementIds.Select(static declaration => declaration.StatementId.Value),
                exportedNode.DeclarationStatementIds);
            Assert.Equal(
                node.PrerequisiteFrozenNodeIds.Select(static id => id.Value),
                exportedNode.PrerequisiteFrozenNodeIds);
        }
    }

    [Fact]
    public void ClosedModuleWithoutAFreezeFailsClosedWithNoOutput()
    {
        var genesisCatalog = BuildCatalog(Module("A"));
        var ledgerFiles = EventFiles(genesisCatalog);
        using var fixture = FixtureFromLedger(ledgerFiles, [Module("A"), Module("B")]);
        using var output = new TemporaryDirectory();

        var (exitCode, console) = Run(fixture, output.Path);

        Assert.Equal(2, exitCode);
        Assert.Contains("TRUTH_EXPORT_REJECTED", console.Error, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(output.Path, "truth-export.v1.json")));
    }

    [Fact]
    public void MissingCandidateLeanReportFileFailsClosedWithNoOutput()
    {
        var genesisCatalog = BuildCatalog(Module("A"));
        var ledgerFiles = EventFiles(genesisCatalog);
        using var fixture = FixtureFromLedger(ledgerFiles, [Module("A")]);
        using var output = new TemporaryDirectory();
        File.Delete(fixture.ReportPath);

        var (exitCode, console) = Run(fixture, output.Path);

        Assert.Equal(2, exitCode);
        Assert.Contains("TRUTH_EXPORT_INVALID", console.Error, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(output.Path, "truth-export.v1.json")));
    }

    [Fact]
    public void ExportReadsAllSemanticBytesFromExactlyOneResolvedRevision()
    {
        var identity = new FrozenRevisionIdentity(
            new string('c', 40),
            "git-sha1:" + new string('c', 40),
            "git-sha1:" + new string('d', 40));
        var committed = Module("A", source: "theorem a : True := by trivial\n");
        var working = Module("A", source: "-- mutable working bytes\ntheorem a : True := by trivial\n");
        var catalog = BuildCatalog(committed);
        var ledgerFiles = EventFiles(catalog);
        using var fixture = FixtureFromLedger(
            ledgerFiles,
            [committed],
            identity,
            workingModules: [working]);
        using var output = new TemporaryDirectory();

        var (exitCode, console) = Run(fixture, output.Path);

        Assert.Equal(0, exitCode);
        Assert.Equal(string.Empty, console.Error);
        var model = ParseExport(output);
        Assert.Equal(new string('c', 40), model.SourceCommit);
        Assert.Equal(new string('d', 40), model.SourceTree);
        Assert.Equal(1, fixture.Gateway.CurrentRevisionResolutionCount);
        Assert.Equal(0, fixture.Gateway.ReadCurrentCount);
        Assert.Equal([identity.Revision], fixture.Gateway.ReadRevisionCalls);
        Assert.Equal(0, fixture.MutableLeanReportSource.CallCount);
        Assert.Equal(
            catalog.ClosedNodes.Single().FrozenNodeId.Value,
            Assert.Single(model.Nodes).FrozenNodeId);
    }

    [Fact]
    public void TwoRunsOnTheSameRevisionAreByteIdentical()
    {
        using var fixture = DivergentLedgerFixture();
        using var first = new TemporaryDirectory();
        using var second = new TemporaryDirectory();

        Assert.Equal(0, Run(fixture, first.Path).ExitCode);
        Assert.Equal(0, Run(fixture, second.Path).ExitCode);

        Assert.Equal(
            TemporaryFileSystem.ReadAllBytes(first, "truth-export.v1.json"),
            TemporaryFileSystem.ReadAllBytes(second, "truth-export.v1.json"));
    }

    [Theory]
    [InlineData("truth-export")]
    [InlineData("truth-export", "--out")]
    [InlineData("truth-export", "--out", "dir")]
    [InlineData("truth-export", "--wrong", "dir")]
    public void UsageErrorsExitOneAndWriteNothing(params string[] arguments)
    {
        using var fixture = DivergentLedgerFixture();
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(arguments, fixture.Environment, console);

        Assert.Equal(1, exitCode);
        Assert.Contains("USAGE", console.Error, StringComparison.Ordinal);
    }

    private static (int ExitCode, BufferedConsole Console) Run(TruthExportFixture fixture, string outDirectory)
    {
        var console = new BufferedConsole();
        var exitCode = CliApplication.Run(
            [
                "truth-export",
                "--out", outDirectory,
                "--candidate-lean-report", fixture.ReportPath,
            ],
            fixture.Environment,
            console);
        return (exitCode, console);
    }

    private static TruthExportFixture DivergentLedgerFixture()
    {
        var originalA = Module("A", source: "theorem a : True := by trivial\n");
        var moduleC = Module("C");

        var finalCatalog = BuildCatalog(originalA, moduleC);
        var ledgerFiles = EventFiles(finalCatalog);
        var fixture = FixtureFromLedger(ledgerFiles, [originalA, moduleC]);
        fixture.LedgerFiles = ledgerFiles;
        fixture.FinalCatalog = finalCatalog;
        return fixture;
    }

    private static TruthExportFixture FixtureFromLedger(
        ImmutableArray<RepositoryFile> ledgerFiles,
        ModuleSpec[] revisionModules,
        FrozenRevisionIdentity? identity = null,
        ModuleSpec[]? workingModules = null)
    {
        var temporary = new TemporaryDirectory();
        var revisionFiles = RepositoryFiles(revisionModules);
        AddLedgerFiles(revisionFiles, ledgerFiles);
        var revisionReports = Reports(revisionModules);
        var immutableRevision = RawSnapshot(revisionFiles);
        var revisionSnapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(immutableRevision)).Snapshot;
        var reportBytes = RawLeanReportArtifact.Write(
            revisionSnapshot,
            LeanAxiomReport.Create(revisionReports));
        var reportPath = Path.Combine(temporary.Path, "candidate-lean-report.json");
        File.WriteAllBytes(reportPath, reportBytes.AsSpan());
        WriteStatementMaterials(reportPath, revisionReports);
        var mutableModules = workingModules ?? revisionModules;
        var mutableFiles = RepositoryFiles(mutableModules);
        AddLedgerFiles(mutableFiles, ledgerFiles);
        var mutableReports = Reports(mutableModules);
        var mutableWorkingTree = RawSnapshot(mutableFiles);
        var mutableLeanReportSource = new FakeLeanReportSource(LeanAxiomReport.Create(mutableReports));
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create([]),
            mutableWorkingTree,
            immutableRevision,
            currentRevisionResolver: identity is null ? null : () => identity);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            gateway,
            mutableLeanReportSource);
        return new TruthExportFixture(
            temporary,
            environment,
            gateway,
            mutableLeanReportSource,
            reportPath,
            reportBytes);
    }

    private static void WriteStatementMaterials(
        string reportPath,
        IReadOnlyDictionary<string, LeanFileReport> reports)
    {
        using var stream = File.Create(RawLeanReportArtifact.MaterialsPath(reportPath));
        using var archive = new ZipArchive(stream, ZipArchiveMode.Create);
        foreach (var declaration in reports.Values
                     .SelectMany(static report => report.Declarations)
                     .DistinctBy(static declaration => declaration.StatementTypeAddress))
        {
            var entry = archive.CreateEntry("sha256/" + declaration.StatementTypeAddress[7..]);
            using var destination = entry.Open();
            destination.Write(Encoding.UTF8.GetBytes(declaration.TypeRepresentation));
        }
    }

    private static Dictionary<string, string> RepositoryFiles(IEnumerable<ModuleSpec> modules)
    {
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["lean-toolchain"] = Toolchain,
            ["lakefile.toml"] = Lakefile,
            ["lake-manifest.json"] = Manifest,
        };
        foreach (var module in modules)
        {
            files[PathFor(module.Name)] = module.Source;
        }

        return files;
    }

    private static Dictionary<string, LeanFileReport> Reports(IEnumerable<ModuleSpec> modules) =>
        modules.ToDictionary(
            static module => PathFor(module.Name),
            ReportFor,
            StringComparer.Ordinal);

    private static RawRepositorySnapshot RawSnapshot(IEnumerable<KeyValuePair<string, string>> files) =>
        RawRepositorySnapshot.Create(
            files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));

    private static ParsedExport ParseExport(TemporaryDirectory output)
    {
        using var document = JsonDocument.Parse(
            TemporaryFileSystem.ReadAllBytes(output, "truth-export.v1.json"));
        var root = document.RootElement;
        var nodes = root.GetProperty("nodes").EnumerateArray()
            .Select(static node => new ParsedExportNode(
                node.GetProperty("repo_path").GetString()!,
                node.GetProperty("frozen_node_id").GetString()!,
                node.GetProperty("node_axiom_closure").EnumerateArray()
                    .Select(static axiom => axiom.GetString()!).ToArray(),
                node.GetProperty("declarations").EnumerateArray()
                    .Select(static declaration => declaration.GetProperty("statement_id").GetString()!)
                    .ToArray(),
                node.GetProperty("prerequisite_frozen_node_ids").EnumerateArray()
                    .Select(static id => id.GetString()!).ToArray()))
            .ToArray();
        return new ParsedExport(
            root.GetProperty("source_commit").GetString()!,
            root.GetProperty("source_tree").GetString()!,
            root.GetProperty("producer").GetString()!,
            nodes);
    }

    private sealed record ParsedExport(
        string SourceCommit,
        string SourceTree,
        string Producer,
        ParsedExportNode[] Nodes);

    private sealed record ParsedExportNode(
        string RepoPath,
        string FrozenNodeId,
        string[] AxiomClosure,
        string[] DeclarationStatementIds,
        string[] PrerequisiteFrozenNodeIds);

    private static class TemporaryFileSystem
    {
        internal static byte[] ReadAllBytes(TemporaryDirectory directory, string fileName)
        {
            if (string.IsNullOrWhiteSpace(fileName) || Path.GetFileName(fileName) != fileName)
            {
                throw new ArgumentException("temporary output name must be a single file name", nameof(fileName));
            }

            return File.ReadAllBytes(Path.Combine(directory.Path, fileName));
        }
    }

    private static LeanFileReport ReportFor(ModuleSpec module)
    {
        var declaration = module.Name.ToLowerInvariant();
        return new LeanFileReport(
            module.Imports.Select(static import => $"D5.S0.Carrier.{import}").ToImmutableArray(),
            ImmutableArray.Create(new LeanDeclaration(
                declaration,
                module.Kind,
                module.StatementMaterial,
                module.Axioms)
            {
                NameKey = $"ns(n0,{declaration.Length}:{declaration})",
                IncludeInStatement = true,
            }));
    }

    private sealed class TruthExportFixture(
        TemporaryDirectory temporary,
        ProductionCliEnvironment environment,
        FakeRepositoryGateway gateway,
        FakeLeanReportSource mutableLeanReportSource,
        string reportPath,
        ImmutableArray<byte> reportBytes) : IDisposable
    {
        internal ProductionCliEnvironment Environment { get; } = environment;

        internal FakeRepositoryGateway Gateway { get; } = gateway;

        internal FakeLeanReportSource MutableLeanReportSource { get; } = mutableLeanReportSource;

        internal string ReportPath { get; } = reportPath;

        internal ImmutableArray<byte> ReportBytes { get; } = reportBytes;

        internal ImmutableArray<RepositoryFile> LedgerFiles { get; set; }

        internal FrozenMaterialCatalog FinalCatalog { get; set; } = null!;

        public void Dispose() => temporary.Dispose();
    }
}
