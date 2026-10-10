using System.Collections.Immutable;
using System.IO.Compression;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed class TruthExportCommandTests
{
    private const string Toolchain = "leanprover/lean4:v4.24.0\n";
    private const string Lakefile = "[package]\nname = \"fixture\"\n";
    private const string Manifest = "{}\n";

    [Theory]
    [InlineData("--list-closed", "--add", "D5/S0/Carrier/A.lean")]
    [InlineData("--list-closed", "--selector", "D5/S0/Carrier/A.lean")]
    [InlineData("--list-closed", "--retire-registration", "D5/S0/Carrier/A.lean")]
    [InlineData("--list-closed", "--from-accepted")]
    [InlineData("--list-closed", "--list-closed")]
    public void ClosedQueryRejectsWriterOptions(params string[] options)
    {
        using var fixture = FixtureFromLedger([], [Module("A")]);
        var console = new BufferedConsole();

        var exit = CliApplication.Run(
            ["ledger-align", .. options, "--candidate-lean-report", fixture.ReportPath],
            fixture.Environment, console);

        Assert.NotEqual(0, exit);
        Assert.Contains("USAGE", console.Error, StringComparison.Ordinal);
        Assert.Equal(0, fixture.Gateway.ReadCurrentCount);
    }

    [Fact]
    public void ClosedQueryReadsUncommittedCurrentModulesInsteadOfHead()
    {
        ModuleSpec[] current = [Module("A"), Module("B", imports: ["A"]),
            Module("C", axioms: ["sorryAx"])];
        using var fixture = FixtureFromLedger([], [Module("A")], workingModules: current);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(RawSnapshot(RepositoryFiles(current)))).Snapshot;
        RawLeanReportArtifact.WriteFile(fixture.ReportPath, snapshot, LeanAxiomReport.Create(Reports(current)));
        var console = new BufferedConsole();

        var exit = CliApplication.Run(
            ["ledger-align", "--list-closed", "--candidate-lean-report", fixture.ReportPath],
            fixture.Environment, console);

        Assert.True(exit == 0, console.Error);
        Assert.Equal(new[] { PathFor("A"), PathFor("B") },
            JsonSerializer.Deserialize<string[]>(console.Output));
        Assert.Equal(1, fixture.Gateway.ReadCurrentCount);
        Assert.Empty(fixture.Gateway.ReadRevisionCalls);
        Assert.Equal(0, fixture.Gateway.CurrentRevisionResolutionCount);
        Assert.False(Directory.Exists(Path.Combine(Path.GetDirectoryName(fixture.ReportPath)!, "Golden")));
    }

    [Fact]
    public void ClosedQueryRejectsReportThatOmitsUncommittedModule()
    {
        using var fixture = FixtureFromLedger([], [Module("A")], workingModules: [Module("A"), Module("B")]);
        var console = new BufferedConsole();

        var exit = CliApplication.Run(
            ["ledger-align", "--list-closed", "--candidate-lean-report", fixture.ReportPath],
            fixture.Environment, console);

        Assert.NotEqual(0, exit);
        Assert.Contains("LEDGER_ALIGN_FAILED", console.Error, StringComparison.Ordinal);
        Assert.Equal(1, fixture.Gateway.ReadCurrentCount);
    }

    [Fact]
    public void ClosedQueryReadsUntrackedModuleInTemporaryRepository()
    {
        using var repository = new TemporaryDirectory();
        using var reports = new TemporaryDirectory();
        var files = RepositoryFiles([Module("A")]);
        foreach (var (path, content) in files)
        {
            var destination = Path.Combine(repository.Path, path);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.WriteAllText(destination, content);
        }
        TestGit.Run(repository.Path, "init");
        TestGit.Run(repository.Path, "config", "user.name", "Closed query fixture");
        TestGit.Run(repository.Path, "config", "user.email", "closed-query@example.invalid");
        TestGit.Run(repository.Path, "add", ".");
        TestGit.Run(repository.Path, "commit", "-m", "Closed A");
        var unrelatedPath = "Meta/Digestion/backfill/unrelated/residual-open/" + new string('a', 64) + ".yaml";
        var unrelatedFullPath = Path.Combine(repository.Path, unrelatedPath);
        Directory.CreateDirectory(Path.GetDirectoryName(unrelatedFullPath)!);
        File.WriteAllBytes(unrelatedFullPath, [0xff]);
        ModuleSpec[] current = [Module("A"), Module("B", imports: ["A"])];
        File.WriteAllText(Path.Combine(repository.Path, PathFor("B")), current[1].Source);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(RawSnapshot(RepositoryFiles(current)))).Snapshot;
        var report = LeanAxiomReport.Create(Reports(current));
        var reportPath = Path.Combine(reports.Path, "candidate-report.json");
        RawLeanReportArtifact.WriteFile(reportPath, snapshot, report);
        var environment = new ProductionCliEnvironment(repository.Path,
            new GitRepositoryGateway(repository.Path), new FakeLeanReportSource(report));
        var console = new BufferedConsole();

        var exit = CliApplication.Run(
            ["ledger-align", "--list-closed", "--candidate-lean-report", reportPath], environment, console);

        Assert.True(exit == 0, console.Error);
        Assert.Equal(new[] { PathFor("A"), PathFor("B") }, JsonSerializer.Deserialize<string[]>(console.Output));
        Assert.Contains("?? " + PathFor("B"), TestGit.Run(repository.Path, "status", "--porcelain"), StringComparison.Ordinal);
        Assert.Equal(string.Empty, TestGit.Run(repository.Path, "ls-tree", "--name-only", "HEAD", PathFor("B")));
    }

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
    public void ClosedModuleWithoutAFreezeExportsProvenTruthWithHonestFreezeStatus()
    {
        var genesisCatalog = BuildCatalog(Module("A"));
        var ledgerFiles = EventFiles(genesisCatalog);
        using var fixture = FixtureFromLedger(ledgerFiles, [Module("A"), Module("B", imports: ["A"])],
            stateModules: [Module("A")]);
        using var output = new TemporaryDirectory();

        var (exitCode, console) = Run(fixture, output.Path);

        Assert.True(exitCode == 0, console.Error);
        using var document = JsonDocument.Parse(
            TemporaryFileSystem.ReadAllBytes(output, "truth-export.v1.json"));
        var root = document.RootElement;
        Assert.Equal(2, root.GetProperty("schema_version").GetInt32());
        Assert.Equal("stratalint.truth-export.v2", root.GetProperty("dialect").GetString());
        var nodes = root.GetProperty("nodes").EnumerateArray().ToArray();
        Assert.Equal(2, nodes.Length);
        Assert.Equal("frozen", nodes[0].GetProperty("freeze_status").GetString());
        Assert.Equal("proven-not-yet-frozen", nodes[1].GetProperty("freeze_status").GetString());
        Assert.Equal(nodes[0].GetProperty("frozen_node_id").GetString(),
            Assert.Single(nodes[1].GetProperty("prerequisite_frozen_node_ids").EnumerateArray()).GetString());
    }

    [Fact]
    public void ProvenCatalogCanBePublishedBeforeAnyFreeze()
    {
        using var fixture = FixtureFromLedger([], [Module("A")]);
        using var output = new TemporaryDirectory();

        var (exitCode, console) = Run(fixture, output.Path);

        Assert.True(exitCode == 0, console.Error);
        using var document = JsonDocument.Parse(
            TemporaryFileSystem.ReadAllBytes(output, "truth-export.v1.json"));
        Assert.Equal("proven-not-yet-frozen", Assert.Single(
            document.RootElement.GetProperty("nodes").EnumerateArray())
            .GetProperty("freeze_status").GetString());
    }

    [Theory]
    [InlineData(true, false, "proven-not-yet-frozen")]
    [InlineData(false, true, "frozen")]
    [InlineData(true, true, "frozen")]
    [InlineData(false, false, "proven-not-yet-frozen")]
    public void FreezeStatusUsesRevisionStateMembership(
        bool hasAcceptedEvent, bool hasState, string expectedStatus)
    {
        var module = Module("A");
        var catalog = BuildCatalog(module);
        var ledgerFiles = hasAcceptedEvent ? EventFiles(catalog) : [];
        using var fixture = FixtureFromLedger(ledgerFiles, [module],
            stateModules: hasState ? [module] : []);
        using var output = new TemporaryDirectory();

        var (exitCode, console) = Run(fixture, output.Path);

        Assert.True(exitCode == 0, console.Error);
        using var document = JsonDocument.Parse(
            TemporaryFileSystem.ReadAllBytes(output, "truth-export.v1.json"));
        var node = Assert.Single(document.RootElement.GetProperty("nodes").EnumerateArray());
        Assert.Equal(PathFor("A"), node.GetProperty("repo_path").GetString());
        Assert.Equal(expectedStatus, node.GetProperty("freeze_status").GetString());
        Assert.Equal(0, fixture.Gateway.ReadCurrentCount);
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void UnfrozenPublicationStillRejectsUnboundSourceOrBrokenClosure(bool unboundSource)
    {
        using var fixture = FixtureFromLedger(EventFiles(BuildCatalog(Module("A"))),
            [Module("A"), Module("B")]);
        using var output = new TemporaryDirectory();
        var files = RepositoryFiles([Module("A"), Module("B", source: "-- other source\n")]);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(RawSnapshot(files))).Snapshot;
        var reports = Reports([Module("A"), Module("B")]);
        if (!unboundSource)
        {
            files = RepositoryFiles([Module("A"), Module("B")]);
            snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
                SnapshotDecoder.Decode(RawSnapshot(files))).Snapshot;
            reports[PathFor("B")] = ReportFor(Module("B")) with { Imports = [" "] };
        }
        File.WriteAllBytes(fixture.ReportPath,
            RawLeanReportArtifact.Write(snapshot, LeanAxiomReport.Create(reports)).AsSpan());

        var (exitCode, console) = Run(fixture, output.Path);

        Assert.Equal(2, exitCode);
        Assert.Contains("TRUTH_EXPORT_INVALID", console.Error, StringComparison.Ordinal);
        Assert.Contains(unboundSource ? "source hash does not match" : "report is malformed",
            console.Error, StringComparison.Ordinal);
        Assert.Empty(Directory.GetFileSystemEntries(output.Path));
    }

    [Fact]
    public void UnfrozenPublicationStillRejectsChangedFrozenIdentity()
    {
        using var fixture = FixtureFromLedger(EventFiles(BuildCatalog(Module("A"))),
            [Module("A") with { StatementMaterial = "False" }, Module("B")]);
        using var output = new TemporaryDirectory();

        var (exitCode, console) = Run(fixture, output.Path);

        Assert.Equal(2, exitCode);
        Assert.Contains("TRUTH_EXPORT_REJECTED", console.Error, StringComparison.Ordinal);
        Assert.Contains("statement identity changed", console.Error, StringComparison.Ordinal);
        Assert.Empty(Directory.GetFileSystemEntries(output.Path));
    }

    [Fact]
    public void UnfrozenPublicationStillRejectsFrozenModuleOutsideClosedCatalog()
    {
        using var fixture = FixtureFromLedger(EventFiles(BuildCatalog(Module("A"))), [Module("B")]);
        using var output = new TemporaryDirectory();

        var (exitCode, console) = Run(fixture, output.Path);

        Assert.Equal(2, exitCode);
        Assert.Contains("outside the current Closed catalog", console.Error, StringComparison.Ordinal);
        Assert.Empty(Directory.GetFileSystemEntries(output.Path));
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
    public void ExportDoesNotRequestDigestionBlobsOrComputeFullProvenance()
    {
        var module = Module("A", source: "theorem a : True := by trivial\n");
        var catalog = BuildCatalog(module);
        using var fixture = FixtureFromLedger(EventFiles(catalog), [module]);
        using var repository = new TemporaryDirectory();
        using var output = new TemporaryDirectory();
        TestGit.Run(repository.Path, "init");
        TestGit.Run(repository.Path, "config", "user.email", "export@example.invalid");
        TestGit.Run(repository.Path, "config", "user.name", "Export Tests");
        foreach (var entry in fixture.Gateway.ReadRevision("fixture").Entries)
        {
            var path = Path.Combine(repository.Path, entry.Path);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllBytes(path, entry.Bytes.AsSpan());
        }
        const string ledgerPath = "Meta/Digestion/backfill/unused/atoms.jsonl";
        var casPath = "Meta/Digestion/atoms/sha256/" + new string('a', 64);
        foreach (var path in new[] { ledgerPath, casPath })
        {
            var full = Path.Combine(repository.Path, path);
            Directory.CreateDirectory(Path.GetDirectoryName(full)!);
            File.WriteAllBytes(full, Enumerable.Repeat((byte)255, 4 * 1024 * 1024).ToArray());
        }
        TestGit.Run(repository.Path, "add", ".");
        TestGit.Run(repository.Path, "commit", "-m", "export inputs");
        var excludedOid = TestGit.Run(repository.Path, "rev-parse", "HEAD:" + casPath).Trim();
        var runner = new GitRepositoryGatewayRevisionTests.CountingBlobGitProcessRunner();
        var result = TruthExportCommand.Run(new GitRepositoryGateway(repository.Path, runner, "git"),
            ["--out", output.Path, "--candidate-lean-report", fixture.ReportPath]);

        Assert.True(result.ExitCode == 0, result.Error);
        Assert.DoesNotContain(excludedOid, runner.BlobsRead);
        Assert.True(runner.BlobOutputBytes < 64 * 1024);
        Assert.Equal(catalog.ClosedNodes.Single().FrozenNodeId.Value, Assert.Single(ParseExport(output).Nodes).FrozenNodeId);
    }

    [Theory]
    [InlineData(null, false)]
    [InlineData("unrelated", false)]
    [InlineData("D5/X_Assumptions/Assumed", true)]
    public void TruthProjectionPreservesTailRegistryEvidenceAndItsRejectionBoundary(string? registration, bool accepted)
    {
        const string path = "D5/X_Assumptions/Assumed.lean";
        using var repository = new TemporaryDirectory();
        TestGit.Run(repository.Path, "init");
        Directory.CreateDirectory(Path.Combine(repository.Path, "D5/X_Assumptions"));
        File.WriteAllText(Path.Combine(repository.Path, path), "axiom marker : Nat\n");
        if (registration is not null)
            File.WriteAllText(Path.Combine(repository.Path, RepositoryPathPolicy.AssumptionRegistryPath), registration + "\n");
        var gateway = new GitRepositoryGateway(repository.Path);
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        { [path] = ReportFor(Module("Assumed", axioms: ["marker"])) });
        foreach (var raw in new[] { gateway.ReadCurrent(), gateway.ReadCurrentProjection(TruthExportCommand.IsTruthInput) })
        {
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
            var truth = DagLedgerCommandPreparation.BuildTruth(snapshot, report);
            var states = LeanTruthStates.Resolve(snapshot, truth.Lean);
            var outcome = FrozenContentAddress.Build(snapshot, truth.Lean, states, LeanImportAdjacency.Build(snapshot, truth.Lean));
            if (accepted)
                Assert.Equal(registration!, Assert.Single(Assert.IsType<FrozenMaterialOutcome.Accepted>(outcome)
                    .Capability.TailRegistrations[RepoPath.CreateKnown(path)]));
            else Assert.IsType<FrozenMaterialOutcome.Rejected>(outcome);
        }
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
        ModuleSpec[]? workingModules = null,
        ModuleSpec[]? stateModules = null)
    {
        var temporary = new TemporaryDirectory();
        var revisionFiles = RepositoryFiles(revisionModules);
        AddLedgerFiles(revisionFiles, ledgerFiles);
        foreach (var module in stateModules ?? [])
        {
            var path = RepoPath.CreateKnown(PathFor(module.Name));
            revisionFiles[FrozenStatePath.FromModulePath(path).Value] = Encoding.UTF8.GetString(
                FrozenStateRecord.Encode(
                    FrozenContentAddress.ComputeModuleStatementId(path, ReportFor(module))).AsSpan());
        }
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
