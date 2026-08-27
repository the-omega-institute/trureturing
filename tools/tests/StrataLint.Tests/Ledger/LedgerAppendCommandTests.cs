using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LedgerAppendCommandTests
{
    [Fact]
    public void RootUsageListsLedgerAppendCommand()
    {
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            Array.Empty<string>(),
            new StubCliEnvironment(new AdmissionOutcome.InfrastructureFailure("unused")),
            console);

        Assert.Equal(2, exitCode);
        Assert.Contains("ledger-append", console.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void LedgerAppendVerbDispatchesToTheEnvironment()
    {
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            new[] { "ledger-append", "--candidate-lean-report", "report.json" },
            new StubCliEnvironment(new AdmissionOutcome.InfrastructureFailure("unused")),
            console);

        Assert.Equal(2, exitCode);
        Assert.Contains("ledger append is not configured", console.Error, StringComparison.Ordinal);
        Assert.DoesNotContain("UNKNOWN_COMMAND", console.Error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("ledger-reattest")]
    [InlineData("ledger-sync")]
    public void RetiredLedgerVerbUsesUnknownCommandFailurePath(string command)
    {
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            new[] { command },
            new StubCliEnvironment(new AdmissionOutcome.InfrastructureFailure("unused")),
            console);

        Assert.Equal(2, exitCode);
        Assert.Equal($"UNKNOWN_COMMAND {command}\n", console.Error);
        Assert.DoesNotContain(command, CliApplication.ImplementedCommands);
    }

    [Fact]
    public void ProductionCommandAppendsEveryMissingFreezeWithoutRewritingTheBaseline()
    {
        using var fixture = new LedgerAppendFixture();
        var baselineLines = FrozenLedgerTestData.Lines(fixture.BaselineBytes);

        var result = fixture.Environment.AppendLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.True(result.Success, result.Error);
        Assert.Contains("appended_freezes=2", result.Output, StringComparison.Ordinal);
        var appendedBytes = FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath);
        var appendedLines = FrozenLedgerTestData.Lines(ImmutableArray.CreateRange(appendedBytes));
        Assert.Equal(baselineLines.Length + 2, appendedLines.Length);
        for (var index = 0; index < baselineLines.Length; index++)
        {
            Assert.Equal(baselineLines[index], appendedLines[index]);
        }

        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(appendedBytes)).Syntax;
        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            FrozenLedgerTestData.ValidateHistory(syntax, fixture.CandidateCatalog));
        Assert.Equal(3, accepted.Capability.ActiveFrozenNodes.Length);
        var persistedFiles = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(fixture.LedgerPath);
        var persistedView = FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            persistedFiles.ToImmutableDictionary(static file => file.Path)));
        Assert.Contains($"head={persistedView.EventSetRoot()}", result.Output, StringComparison.Ordinal);
        Assert.Equal(
            new[]
            {
                FrozenLedgerTestData.PathFor("B"),
                FrozenLedgerTestData.PathFor("C"),
            },
            accepted.Capability.Events
                .OfType<FrozenLedgerEvent.Freeze>()
                .Skip(1)
                .Select(static item => item.Payload.Input.DescriptorSelector)
                .Order(StringComparer.Ordinal));
    }

    [Fact]
    public void ProductionCommandWithOneAppendValidatesOnlyTheSuffixOids()
    {
        using var fixture = new LedgerAppendFixture(addSecondClosedModule: false);
        var preparation = DagLedgerCommandPreparation.Prepare(
            fixture.Root,
            fixture.Gateway,
            fixture.ReportPath);

        Assert.Equal(2, preparation.BaseView.EventCount);

        var result = fixture.Environment.AppendLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.True(result.Success, result.Error);
        Assert.Contains("appended_freezes=1", result.Output, StringComparison.Ordinal);
        var references = Assert.Single(fixture.Gateway.FrozenReferenceValidations);
        Assert.Single(references.Inputs);
        Assert.Equal(FrozenLedgerTestData.PathFor("B"), references.Inputs[0].DescriptorSelector);
        Assert.DoesNotContain(
            references.Inputs,
            static input => input.DescriptorSelector == FrozenLedgerTestData.PathFor("A"));
        Assert.Single(references.CommitOids);
        Assert.Single(references.TreeOids);
        Assert.Equal(3, references.BlobOids.Length);
    }

    [Fact]
    public void ProductionCommandTreatsRepresentationDriftAsNoOpWithoutWriting()
    {
        using var fixture = new LedgerAppendFixture(
            driftARepresentation: true,
            addSecondClosedModule: false,
            reportADriftInChangeSet: true,
            aImportsB: true);
        var before = FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath);
        var result = fixture.Environment.AppendLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.True(result.Success, result.Error);
        Assert.Contains("no catalog reconciliation required", result.Output, StringComparison.Ordinal);
        Assert.Contains("appended_freezes=0", result.Output, StringComparison.Ordinal);
        Assert.Equal(before, FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
    }

    [Fact]
    public void WriterPreparationBuildsOnlyCandidateDeltaAndTrustsCommittedBaseIdentity()
    {
        using var fixture = new LedgerAppendFixture(currentAStatementMaterial: "False");

        var preparation = DagLedgerCommandPreparation.Prepare(
            fixture.Root,
            fixture.Gateway,
            fixture.ReportPath);

        Assert.Equal(
            new[] { FrozenLedgerTestData.PathFor("B"), FrozenLedgerTestData.PathFor("C") },
            preparation.Catalog.ClosedNodes.Select(static node => node.RepoPath.Value));

        var result = fixture.Environment.AppendLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.True(result.Success, result.Error);
        Assert.Contains("appended_freezes=2", result.Output, StringComparison.Ordinal);

        using var dependencyFixture = new LedgerAppendFixture(
            addSecondClosedModule: false,
            aImportsB: true,
            reportBDriftInChangeSet: true);
        var dependencyPreparation = DagLedgerCommandPreparation.Prepare(
            dependencyFixture.Root,
            dependencyFixture.Gateway,
            dependencyFixture.ReportPath);
        Assert.Equal(
            new[] { FrozenLedgerTestData.PathFor("A"), FrozenLedgerTestData.PathFor("B") },
            dependencyPreparation.Catalog.ClosedNodes.Select(static node => node.RepoPath.Value));

    }

    [Fact]
    public void WriterPreparationDoesNotRehashAnUnchangedClosedDescriptor()
    {
        using var fixture = new LedgerAppendFixture(
            driftARepresentation: true,
            reportADriftInChangeSet: false);

        var preparation = DagLedgerCommandPreparation.Prepare(
            fixture.Root,
            fixture.Gateway,
            fixture.ReportPath);

        Assert.Equal(
            new[] { FrozenLedgerTestData.PathFor("B"), FrozenLedgerTestData.PathFor("C") },
            preparation.Catalog.ClosedNodes.Select(static node => node.RepoPath.Value));
    }

    [Fact]
    public void ProductionCommandReportsNoMissingFreezesWithoutWritingAgain()
    {
        using var fixture = new LedgerAppendFixture();
        var first = fixture.Environment.AppendLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });
        Assert.True(first.Success, first.Error);
        var appendedBytes = FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath);

        var second = fixture.Environment.AppendLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.True(second.Success, second.Error);
        Assert.Contains("no catalog reconciliation required", second.Output, StringComparison.Ordinal);
        Assert.Contains("appended_freezes=0", second.Output, StringComparison.Ordinal);
        Assert.Equal(appendedBytes, FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
    }

    /// The preparation step marks an unusable raw report with its own exception type. Drop that
    /// type from this command's catch list and the failure escapes with no LEDGER_APPEND_FAILED
    /// diagnostic at all -- which is exactly how a real contract break went unnoticed here.
    [Fact]
    public void ProductionCommandKeepsItsDiagnosticWhenTheReportCannotBeLoaded()
    {
        using var fixture = new LedgerAppendFixture();
        File.WriteAllText(fixture.ReportPath, "this is not a raw Lean report");

        var result = fixture.Environment.AppendLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.False(result.Success, result.Output);
        Assert.StartsWith("LEDGER_APPEND_FAILED ", result.Error, StringComparison.Ordinal);
        // The marker's own message says only "raw Lean report is unusable". Reporting that instead
        // of the cause would silently drop the diagnostic this command had before the marker existed.
        Assert.Contains("Raw Lean report is not valid JSON.", result.Error, StringComparison.Ordinal);
    }

    /// The gateway is asked before the report is read, so this reaches the other marker type and
    /// no other. Orthogonal to the report case above: neither mutant kills both tests.
    [Fact]
    public void ProductionCommandKeepsItsDiagnosticWhenTheRepositoryCannotBeRead()
    {
        using var fixture = new LedgerAppendFixture();
        var environment = new ProductionCliEnvironment(
            fixture.Root,
            new FakeRepositoryGateway(RawChangeSet.Create([]), null, null),
            new FakeLeanReportSource(null));

        var result = environment.AppendLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.False(result.Success, result.Output);
        Assert.StartsWith("LEDGER_APPEND_FAILED ", result.Error, StringComparison.Ordinal);
        Assert.Contains("current snapshot should not be read", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void PublicHistoryValidationStillRejectsAnIncompleteClosedCatalog()
    {
        using var fixture = new LedgerAppendFixture();
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(fixture.BaselineBytes.AsSpan())).Syntax;

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            FrozenLedgerTestData.ValidateHistory(syntax, fixture.CandidateCatalog));

        Assert.Contains("missing Freeze", rejected.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void WriteNewEventsRejectsABaselineChangedAfterTheEarlyRecheckWithoutWriting()
    {
        using var temporary = new TemporaryDirectory();
        var (baselineBytes, baseline, candidateCatalog) = ReconciliationFixture(includeNewModule: true);
        var candidateBytes = FrozenLedgerGenerator.AppendMissingFreezes(baseline, candidateCatalog);
        var candidateSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(candidateBytes.AsSpan())).Syntax;
        FrozenLedgerTestData.WriteLedgerDirectory(temporary.Path, baselineBytes);
        var expectedBaselineFiles = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(
            temporary.Path);
        Assert.True(DagLedgerCommandPreparation.LoadLedgerDirectory(
                temporary.Path,
                "early baseline recheck").RawBytes.AsSpan().SequenceEqual(baselineBytes.AsSpan()));

        const string competing = "-- competing representation\ntheorem a : True := by trivial\n";
        var competingCatalog = FrozenLedgerTestData.BuildCatalog(
            FrozenLedgerTestData.Module("A", source: competing),
            FrozenLedgerTestData.Module("C", imports: new[] { "A" }));
        var competingBytes = FrozenLedgerGenerator.AppendMissingFreezes(baseline, competingCatalog);
        var competingSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(competingBytes.AsSpan())).Syntax;
        DagLedgerAppendWriter.WriteNewEvents(
            temporary.Path,
            competingSyntax.Lines,
            baseline.Events.Length);
        var before = DirectorySnapshot(temporary.Path);

        var exception = Assert.Throws<InvalidOperationException>(() =>
            DagLedgerAppendWriter.WriteNewEvents(
                temporary.Path,
                candidateSyntax.Lines,
                baseline.Events.Length,
                expectedBaselineFiles: expectedBaselineFiles));

        Assert.Contains("accepted event files changed", exception.Message, StringComparison.Ordinal);
        var after = DirectorySnapshot(temporary.Path);
        Assert.Equal(before.Keys, after.Keys);
        Assert.All(before, item => Assert.Equal(item.Value, after[item.Key]));
        Assert.Empty(Directory.EnumerateDirectories(temporary.Path, ".ledger-stage-*"));
    }

    [Fact]
    public void PublicationLockBlocksASecondWriterAndProtectsItsStageUntilRelease()
    {
        using var temporary = new TemporaryDirectory();
        var lockPath = Path.Combine(temporary.Path, ".ledger-write.lock");
        var activeStage = Path.Combine(temporary.Path, ".ledger-stage-active");
        Directory.CreateDirectory(activeStage);
        File.WriteAllText(Path.Combine(activeStage, "pending.json"), "pending\n");

        using (DagLedgerAppendWriter.AcquirePublicationLock(lockPath))
        {
            var exception = Assert.Throws<IOException>(() => DagLedgerAppendWriter.WriteNewEvents(
                temporary.Path,
                Array.Empty<FrozenLedgerLineSyntax>()));

            Assert.Contains("owns the writer lock", exception.Message, StringComparison.Ordinal);
            Assert.True(Directory.Exists(activeStage));
        }

        DagLedgerAppendWriter.WriteNewEvents(
            temporary.Path,
            Array.Empty<FrozenLedgerLineSyntax>());

        Assert.False(Directory.Exists(activeStage));
    }

    [Fact]
    public void WriteNewEventsReapsStaleStagingDirectoriesBeforePlanning()
    {
        using var temporary = new TemporaryDirectory();
        var stale = Path.Combine(temporary.Path, ".ledger-stage-stale");
        Directory.CreateDirectory(stale);
        File.WriteAllText(Path.Combine(stale, "orphan.json"), "orphan\n");

        DagLedgerAppendWriter.WriteNewEvents(
            temporary.Path,
            Array.Empty<FrozenLedgerLineSyntax>());

        Assert.False(Directory.Exists(stale));
    }

    [Fact]
    public void RepositoryIgnoresLedgerPublicationScratchArtifacts()
    {
        var ignore = File.ReadAllLines(Path.Combine(TestRepositoryLayout.FindRoot(), ".gitignore"));

        Assert.Contains("/Golden/Frozen/accepted/.ledger-stage-*/", ignore);
        Assert.Contains("/Golden/Frozen/accepted/.ledger-write.lock", ignore);
    }

    private static (
        ImmutableArray<byte> BaselineBytes,
        FrozenLedgerConsistent Baseline,
        FrozenMaterialCatalog CandidateCatalog) ReconciliationFixture(bool includeNewModule)
    {
        const string original = "theorem a : True := by trivial\n";
        const string changed = "-- representation changed\ntheorem a : True := by trivial\n";
        var baselineCatalog = FrozenLedgerTestData.BuildCatalog(
            FrozenLedgerTestData.Module("A", source: original));
        var candidateModules = new List<FrozenLedgerTestData.ModuleSpec>
        {
            FrozenLedgerTestData.Module("A", source: changed),
        };
        if (includeNewModule)
        {
            candidateModules.Add(FrozenLedgerTestData.Module("B", imports: new[] { "A" }));
        }

        var candidateCatalog = FrozenLedgerTestData.BuildCatalog(candidateModules.ToArray());
        var baselineBytes = FrozenLedgerGenerator.GenerateGenesis(
            baselineCatalog,
            new FrozenGenesisDescriptor(
                FrozenLedgerTestData.GitOid('e'),
                RuleCatalog.Default.RootSha256));
        var baselineSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(baselineBytes.AsSpan())).Syntax;
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            FrozenLedgerTestData.ValidateGenesis(baselineSyntax, baselineCatalog)).Capability;
        return (baselineBytes, baseline, candidateCatalog);
    }

    private static SortedDictionary<string, byte[]> DirectorySnapshot(string directory)
    {
        var result = new SortedDictionary<string, byte[]>(StringComparer.Ordinal);
        foreach (var path in Directory.EnumerateFiles(directory))
        {
            result.Add(Path.GetFileName(path), File.ReadAllBytes(path));
        }

        return result;
    }

    internal sealed class LedgerAppendFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();

        internal LedgerAppendFixture(
            bool driftARepresentation = false,
            string currentAStatementMaterial = "True",
            bool pinBump = false,
            bool addSecondClosedModule = true,
            bool reportADriftInChangeSet = false,
            bool aImportsB = false,
            bool reportBDriftInChangeSet = false,
            bool aImportsExternal = false,
            bool externalPackagePinned = false,
            bool externalPackagePinBump = false,
            bool externalPackageManifestOnlyDrift = false)
        {
            if ((externalPackagePinBump || externalPackageManifestOnlyDrift)
                && !externalPackagePinned)
            {
                throw new ArgumentException(
                    "An external package pin delta requires a pinned external package.");
            }

            var externalImport = externalPackagePinned ? "Mathlib.Foo" : "External.Foo";
            const string baselineToolchain = "leanprover/lean4:v4.24.0\n";
            var currentToolchain = pinBump
                ? "leanprover/lean4:v4.25.0\n"
                : baselineToolchain;
            const string lakefile = "[package]\nname = \"fixture\"\n";
            var baselineManifest = externalPackagePinned
                ? "{\"packages\":[{\"name\":\"mathlib\",\"type\":\"git\",\"rev\":\"abc123\"}]}\n"
                : "{}\n";
            var currentManifest = externalPackagePinBump
                ? "{\"packages\":[{\"name\":\"mathlib\",\"type\":\"git\",\"rev\":\"def456\"}]}\n"
                : externalPackageManifestOnlyDrift
                    ? "{\"packages\":[{\"name\":\"mathlib\",\"type\":\"git\",\"rev\":\"abc123\",\"metadata\":\"changed\"}]}\n"
                    : baselineManifest;
            var aSource = aImportsB
                ? "import D5.S0.Carrier.B\ntheorem a : B.P := B.proof\n"
                : aImportsExternal
                    ? $"import {externalImport}\ntheorem a : External.P := External.proof\n"
                    : "theorem a : True := by trivial\n";
            var baselineA = FrozenLedgerTestData.ModuleWithReport(
                "A",
                aSource,
                aImportsExternal ? "Nat.Prime 2" : "True") with
            {
                Imports = aImportsB
                    ? ImmutableArray.Create("B")
                    : aImportsExternal
                        ? ImmutableArray.Create(externalImport)
                        : ImmutableArray<string>.Empty,
            };
            var candidateA = FrozenLedgerTestData.ModuleWithReport(
                "A",
                driftARepresentation
                    ? "-- representation changed\ntheorem a : True := by trivial\n"
                    : baselineA.Source,
                currentAStatementMaterial) with
            {
                Imports = baselineA.Imports,
            };
            var baselineB = aImportsB
                ? FrozenLedgerTestData.Module(
                    "B",
                    source: "namespace B\ndef P : Prop := Nat.Prime 2\ntheorem proof : P := by decide\nend B\n")
                : null;
            var candidateB = aImportsB
                ? FrozenLedgerTestData.Module(
                    "B",
                    source: reportBDriftInChangeSet
                        ? "namespace B\ndef P : Prop := True\ntheorem proof : P := trivial\nend B\n"
                        : baselineB!.Source)
                : FrozenLedgerTestData.Module("B", imports: new[] { "A" });
            var c = FrozenLedgerTestData.Module("C", imports: new[] { "B" });
            var baselineCatalog = aImportsB
                ? FrozenLedgerTestData.BuildCatalogWithEnvironment(
                    baselineToolchain,
                    lakefile,
                    baselineManifest,
                    FrozenLedgerTestData.GitOid('a'),
                    FrozenLedgerTestData.GitOid('b'),
                    baselineA,
                    baselineB!)
                : FrozenLedgerTestData.BuildCatalogWithEnvironment(
                    baselineToolchain,
                    lakefile,
                    baselineManifest,
                    FrozenLedgerTestData.GitOid('a'),
                    FrozenLedgerTestData.GitOid('b'),
                    baselineA);
            CandidateCatalog = addSecondClosedModule
                ? FrozenLedgerTestData.BuildCatalogWithEnvironment(
                    currentToolchain,
                    lakefile,
                    currentManifest,
                    FrozenLedgerTestData.GitOid('a'),
                    FrozenLedgerTestData.GitOid('b'),
                    candidateA,
                    candidateB,
                    c)
                : FrozenLedgerTestData.BuildCatalogWithEnvironment(
                    currentToolchain,
                    lakefile,
                    currentManifest,
                    FrozenLedgerTestData.GitOid('a'),
                    FrozenLedgerTestData.GitOid('b'),
                    candidateA,
                    candidateB);
            BaselineBytes = FrozenLedgerGenerator.GenerateGenesis(
                baselineCatalog,
                new FrozenGenesisDescriptor(
                    FrozenLedgerTestData.GitOid('e'),
                    RuleCatalog.Default.RootSha256));
            var files = new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["lean-toolchain"] = currentToolchain,
                ["lakefile.toml"] = lakefile,
                ["lake-manifest.json"] = currentManifest,
                [FrozenLedgerTestData.PathFor("A")] = candidateA.Source,
                [FrozenLedgerTestData.PathFor("B")] = candidateB.Source,
            };
            if (addSecondClosedModule)
            {
                files.Add(FrozenLedgerTestData.PathFor("C"), c.Source);
            }
            FrozenLedgerTestData.AddLedgerFiles(files, BaselineBytes);
            var baselineFiles = new Dictionary<string, string>(files, StringComparer.Ordinal)
            {
                ["lean-toolchain"] = baselineToolchain,
                ["lakefile.toml"] = lakefile,
                ["lake-manifest.json"] = baselineManifest,
                [FrozenLedgerTestData.PathFor("A")] = baselineA.Source,
            };
            if (baselineB is not null)
            {
                baselineFiles[FrozenLedgerTestData.PathFor("B")] = baselineB.Source;
            }
            var raw = RawRepositorySnapshot.Create(
                files.Select(static item => RawRepositoryEntry.FromText(item.Key, item.Value)));
            var baselineRaw = RawRepositorySnapshot.Create(
                baselineFiles.Select(static item => new RawRepositoryEntry(
                    item.Key,
                    ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(item.Value)),
                    FrozenLedgerTestData.GitBlobOid(item.Value))));
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
                SnapshotDecoder.Decode(raw)).Snapshot;
            var reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            {
                [FrozenLedgerTestData.PathFor("A")] = Report(
                    "A",
                    currentAStatementMaterial,
                    aImportsB
                        ? new[] { "B" }
                        : aImportsExternal
                            ? new[] { externalImport }
                            : Array.Empty<string>()),
                [FrozenLedgerTestData.PathFor("B")] = Report(
                    "B",
                    "True",
                    aImportsB ? Array.Empty<string>() : new[] { "A" }),
            };
            if (addSecondClosedModule)
            {
                reports.Add(FrozenLedgerTestData.PathFor("C"), Report("C", "True", ["B"]));
            }
            var report = LeanAxiomReport.Create(reports);

            LedgerPath = Path.Combine(
                temporary.Path,
                FrozenLedgerChangeClassifier.AcceptedRoot.Replace('/', Path.DirectorySeparatorChar));
            FrozenLedgerTestData.WriteLedgerDirectory(LedgerPath, BaselineBytes);
            ReportPath = Path.Combine(temporary.Path, "candidate-lean-report.json");
            RawLeanReportArtifact.WriteFile(ReportPath, snapshot, report);
            Gateway = new FakeRepositoryGateway(
                RawChangeSet.Create(
                    (reportADriftInChangeSet
                        ? new[] { FrozenLedgerTestData.PathFor("A") }
                        : Array.Empty<string>())
                    .Concat(reportBDriftInChangeSet
                        ? new[] { FrozenLedgerTestData.PathFor("B") }
                        : Array.Empty<string>())),
                raw,
                baselineRaw);
            Environment = new ProductionCliEnvironment(
                temporary.Path,
                Gateway,
                new FakeLeanReportSource(null));
        }

        internal ImmutableArray<byte> BaselineBytes { get; }

        internal FrozenMaterialCatalog CandidateCatalog { get; }

        internal ProductionCliEnvironment Environment { get; }

        internal FakeRepositoryGateway Gateway { get; }

        internal string LedgerPath { get; }

        internal string ReportPath { get; }

        internal string Root => temporary.Path;

        public void Dispose() => temporary.Dispose();

        private static LeanFileReport Report(
            string name,
            string statementMaterial,
            IEnumerable<string>? imports = null) => new(
            (imports ?? []).Select(static item => item.Contains('.', StringComparison.Ordinal)
                    ? item
                    : $"D5.S0.Carrier.{item}")
                .ToImmutableArray(),
            ImmutableArray.Create(new LeanDeclaration(
                name.ToLowerInvariant(),
                "theorem",
                statementMaterial,
                ImmutableArray<string>.Empty)
            {
                NameKey = $"ns(n0,{name.Length}:{name.ToLowerInvariant()})",
            }));
    }
}
