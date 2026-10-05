using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.CoverBatch.Tests;

public sealed partial class CoverBatchCommandTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CliDispatchesBatchAndPreservesInputErrorExitCode(bool unavailableScribe)
    {
        using var world = new BatchWorld();
        var environment = new ProductionCliEnvironment(world.Root, world.Repository, world.Report,
            unavailableScribe ? null : new CallbackVerifier(() => { }), CoverWorld.TimeProvider);
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(["cover-batch"], environment, console);

        Assert.Equal(2, exitCode);
        Assert.Contains("COVER_BATCH_INPUT_INVALID", console.Error, StringComparison.Ordinal);
        Assert.Equal(0, world.Repository.ReadCount);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CoverBatchWritesCoverageWithoutCallingScribeVerifier(bool unavailableScribe)
    {
        const string definitionPath = "Blueprint/D5/S0/Carrier/Probe.scribe.cs";
        using var world = new BatchWorld { UseGitReader = true };
        WriteScribeFixture(world.Root, definitionPath, "invalid C#");
        TestGit.Run(world.Root, "init", "--quiet");
        var inputPath = Path.Combine(world.Root, "atoms.tsv");
        File.WriteAllText(inputPath, Row(First, Gid) + Row(Second, OtherGid));
        var calls = 0;
        var environment = new ProductionCliEnvironment(world.Root, world.Repository, world.Report,
            unavailableScribe ? null : new CallbackVerifier(() =>
            {
                calls++;
                throw new InvalidOperationException("Scribe must not execute during cover-batch");
            }), CoverWorld.TimeProvider);

        var result = environment.CoverBatch(["--atoms", inputPath]);

        Assert.True(result.Success, result.Error + result.Output);
        Assert.Equal(0, calls);
        Assert.Equal(["applied", "applied"], Results(result).Select(item => item.Status).ToArray());
        Assert.Equal([Gid], world.Entry(First).CoverageGids.ToArray());
        Assert.Equal([OtherGid], world.Entry(Second).CoverageGids.ToArray());
    }

    [Theory]
    [InlineData("")]
    [InlineData("atom D5/S0/Carrier/Probe.probe\n")]
    [InlineData("atom\tD5/S0/Carrier/Probe.probe\textra\n")]
    [InlineData("INVALID\tD5/S0/Carrier/Probe.probe\n")]
    [InlineData("atom\tD5/S0/Carrier/Probe\n")]
    [InlineData("atom\tD5/S0/Carrier/Probe.probe\r\n")]
    public void InvalidInputIsRejectedBeforeLoadingOrWriting(string input)
    {
        using var world = new BatchWorld();
        var before = world.LedgerImage();

        var result = world.Run(input);

        Assert.Equal(2, result.ExitCode);
        Assert.Equal(0, world.Repository.ReadCount);
        Assert.Equal(0, world.Report.CallCount);
        Assert.DoesNotContain(StrataLint.Scribe.CanonicalValuesWriter.RelativePath, result.Output, StringComparison.Ordinal);
        Assert.Equal(before, world.LedgerImage());
    }

    [Fact]
    public void DuplicateAtomsMergeGidsAndLoadSharedDependenciesOnce()
    {
        using var world = new BatchWorld();

        var result = world.Run(Row(First, Gid) + Row(Second, Gid)
            + Row(First, OtherGid) + Row(First, Gid));

        Assert.True(result.Success, result.Error + result.Output);
        Assert.Equal(0, result.ExitCode);
        Assert.Equal(["applied", "applied"], Results(result).Select(item => item.Status).ToArray());
        Assert.Equal([1, 3, 4], Results(result)[0].Lines);
        Assert.Equal([OtherGid, Gid], world.Entry(First).CoverageGids.ToArray());
        // One session reads its scope and then the paths the ledger declares.
        Assert.Equal(2, world.Repository.ScopedCurrentReads.Count);
        Assert.Equal(0, world.Repository.WholeTreeReadCount);
        Assert.Empty(world.Repository.ReadRevisionCalls);
        Assert.Empty(world.Repository.ReadChangesCalls);
        Assert.Equal(1, world.Report.CallCount);
        Assert.Single(result.Output.Split('\n'), line =>
            line.Contains(StrataLint.Scribe.CanonicalValuesWriter.RelativePath, StringComparison.Ordinal));
    }

    [Fact]
    public void IndependentFailureContinuesAndPartialSuccessEmitsValuesOnce()
    {
        using var world = new BatchWorld();

        var result = world.Run(Row(First, MissingGid) + Row(Second, Gid));

        Assert.Equal(1, result.ExitCode);
        Assert.Equal(["failed", "applied"], Results(result).Select(item => item.Status).ToArray());
        Assert.Empty(world.Entry(First).Coverage);
        Assert.Single(world.Entry(Second).Coverage);
        Assert.Single(result.Output.Split('\n'), line =>
            line.Contains(StrataLint.Scribe.CanonicalValuesWriter.RelativePath, StringComparison.Ordinal));
    }

    [Fact]
    public void InvalidGidInMergedRequestDoesNotLeavePartialCoverage()
    {
        using var world = new BatchWorld();

        var result = world.Run(Row(First, Gid) + Row(Second, Gid) + Row(First, MissingGid));

        Assert.Equal(["failed", "applied"], Results(result).Select(item => item.Status).ToArray());
        Assert.Equal([1, 3], Results(result)[0].Lines);
        Assert.Empty(world.Entry(First).Coverage);
        Assert.Single(world.Entry(Second).Coverage);
    }

    [Fact]
    public void FailurePropagatesThroughUnrequestedIntermediate()
    {
        using var world = new BatchWorld(entry => entry with
        {
            Receipts = entry.Receipts with { ChainAtoms = [entry.AtomId == First ? Second : "missing-atom"] },
        });

        var result = world.Run(Row(First, Gid) + Row("missing-atom", Gid));

        Assert.Equal(["failed", "blocked"], Results(result).Select(item => item.Status).ToArray());
        Assert.Contains("missing-atom", Results(result)[1].Reason, StringComparison.Ordinal);
        Assert.Empty(world.Entry(First).Coverage);
    }

    [Fact]
    public void BatchReadsItsScopeOnceAcrossItsOwnLedgerMigrations()
    {
        using var world = new BatchWorld { UseGitReader = true };
        TestGit.Run(world.Root, "init");

        var result = world.Run(Row(First, Gid) + Row(Second, OtherGid));

        Assert.True(result.Success, result.Error + result.Output);
        Assert.Equal(["applied", "applied"], Results(result).Select(item => item.Status).ToArray());
        Assert.Equal(2, world.Repository.ScopedCurrentReads.Count);
        Assert.Equal(0, world.Repository.WholeTreeReadCount);
    }

    [Fact]
    public void SameInputsMatchSequentialTransactionsWithOneSharedLoad()
    {
        using var sequential = new BatchWorld();
        using var batch = new BatchWorld();
        LedgerLoadCounter sequentialLoads;
        using (sequentialLoads = new LedgerLoadCounter()) sequential.RunSingles();
        LedgerLoadCounter batchLoads;
        CommandResult result;
        using (batchLoads = new LedgerLoadCounter()) result = batch.Run(Row(First, Gid) + Row(Second, OtherGid));

        Assert.True(result.Success, result.Error + result.Output);
        Assert.Equal(sequential.LedgerImage(), batch.LedgerImage());
        Assert.Equal(4, sequential.Repository.ScopedCurrentReads.Count);
        Assert.Empty(sequential.Repository.ReadRevisionCalls);
        Assert.Equal(2, sequential.Report.CallCount);
        Assert.Equal(2, batch.Repository.ScopedCurrentReads.Count);
        Assert.Empty(batch.Repository.ReadRevisionCalls);
        Assert.Equal(1, batch.Report.CallCount);
        WriteLoadCounts("identical-input-sequential", sequentialLoads);
        WriteLoadCounts("identical-input-batch", batchLoads);
        Assert.Equal(0, sequentialLoads.BaselineLoads);
        Assert.Equal([1, 1], sequentialLoads.CandidateSnapshotLoads);
        Assert.Equal(0, batchLoads.BaselineLoads);
        Assert.Equal([1, 1], batchLoads.CandidateSnapshotLoads);
    }

    [Theory]
    [InlineData("\n# stored-byte oracle witness\n")]
    [InlineData("\n \n")]
    public void NonsemanticStoredBytesAreVisibleToBatchLedgerOracle(string suffix)
    {
        using var world = new BatchWorld();
        var path = world.LedgerPaths().Single(path => path.EndsWith(First + ".yaml", StringComparison.Ordinal));
        var before = world.LedgerImage();
        var semanticBefore = DirectoryLedgerTestSupport.Image(BackfillInventoryLoader.LoadRoot(world.Root));

        File.AppendAllText(path, suffix);

        Assert.Equal(semanticBefore, DirectoryLedgerTestSupport.Image(BackfillInventoryLoader.LoadRoot(world.Root)));
        Assert.NotEqual(before, world.LedgerImage());
    }

    [Fact]
    public void SessionKeepsTheChangeKindsOfItsOwnWritesAfterRepeatedWrites()
    {
        using var world = new BatchWorld();
        var session = new CoverAtomCommand.Session(world.Root, world.Repository, world.Report,
            CoverWorld.FixtureUtc, Gid);
        Assert.True(session.Apply(First, [Gid]).Success);
        Assert.True(session.Apply(First, [OtherGid]).Success);

        Assert.Equal(RawChangeKind.Added, Assert.Single(session.Changes.Entries,
            change => change.Path.Value.EndsWith("absorbed-closed/" + First + ".yaml", StringComparison.Ordinal)).Kind);
        Assert.Equal(RawChangeKind.Deleted, Assert.Single(session.Changes.Entries,
            change => change.Path.Value.EndsWith("residual-open/" + First + ".yaml", StringComparison.Ordinal)).Kind);
    }

    [Fact]
    public void TerminalFailureDispositionAdvancesSessionAndDoesNotPreventIndependentWrite()
    {
        using var world = new BatchWorld(entry => entry.AtomId == First
            ? entry with { Receipts = entry.Receipts with { UnresolvedSubitems = ["remaining clause"] } }
            : entry);

        var result = world.Run(Row(First, Gid) + Row(Second, Gid));

        Assert.Equal(["failed", "applied"], Results(result).Select(item => item.Status).ToArray());
        Assert.NotNull(world.Entry(First).Receipts.CoverDisposition);
        Assert.Empty(world.Entry(First).Coverage);
        Assert.Single(world.Entry(Second).Coverage);
        Assert.Single(result.Output.Split('\n'), line =>
            line.Contains(StrataLint.Scribe.CanonicalValuesWriter.RelativePath, StringComparison.Ordinal));
    }

    [Fact]
    public void DependencyExecutesBeforeParentAndMovesAncestorState()
    {
        using var world = new BatchWorld(chain: true);

        var result = world.Run(Row(world.ParentId!, OtherGid)
            + Row(world.ChildIds[0], Gid) + Row(world.ChildIds[1], OtherGid));

        Assert.True(result.Success, result.Error + result.Output);
        Assert.Equal([world.ChildIds[0], world.ChildIds[1], world.ParentId!],
            Results(result).Select(item => item.AtomId).ToArray());
        Assert.Equal(DigestionMigrationState.Absorbed, world.Entry(world.ParentId!).ProjectedStatus.Migration);
        Assert.Equal(DigestionTruthState.Closed, world.Entry(world.ParentId!).ProjectedStatus.Truth);
        Assert.DoesNotContain(world.LedgerPaths(), path => path.Contains("residual-open", StringComparison.Ordinal));
    }

    [Fact]
    public void DependencyFailureBlocksParent()
    {
        using var world = new BatchWorld(entry => entry.AtomId == First
            ? entry with { Receipts = entry.Receipts with { ChainAtoms = [Second] } }
            : entry);

        var result = world.Run(Row(First, Gid) + Row(Second, MissingGid));

        Assert.Equal(["failed", "blocked"], Results(result).Select(item => item.Status).ToArray());
        Assert.Contains(Second, Results(result)[1].Reason, StringComparison.Ordinal);
        Assert.Empty(world.Entry(First).Coverage);
        Assert.Null(world.Entry(First).Receipts.CoverDisposition);
        Assert.Single(result.Output.Split('\n'), line =>
            line.Contains(StrataLint.Scribe.CanonicalValuesWriter.RelativePath, StringComparison.Ordinal));
    }

    [Fact]
    public void RelevantDependencyCycleIsRejectedBeforeAnyWrites()
    {
        using var world = new BatchWorld(entry => entry with
        {
            Receipts = entry.Receipts with { ChainAtoms = [entry.AtomId == First ? Second : First] },
        });
        var before = world.LedgerImage();

        var result = world.Run(Row(First, Gid));

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("cycle", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Equal(before, world.LedgerImage());
        Assert.DoesNotContain(StrataLint.Scribe.CanonicalValuesWriter.RelativePath, result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void RerunValidatesExistingBindingsAndRecoversFailedItem()
    {
        using var world = new BatchWorld();
        Assert.False(world.Run(Row(First, Gid) + Row(Second, MissingGid)).Success);
        var appliedPath = world.LedgerPaths().Single(path => path.EndsWith(First + ".yaml", StringComparison.Ordinal));
        var appliedBytes = TemporaryFileSystem.File.ReadAllBytes(appliedPath);

        var result = world.Run(Row(First, Gid) + Row(Second, OtherGid));

        Assert.True(result.Success, result.Error + result.Output);
        Assert.Equal(["already_applied", "applied"], Results(result).Select(item => item.Status).ToArray());
        Assert.Equal(appliedBytes, TemporaryFileSystem.File.ReadAllBytes(appliedPath));
        Assert.Single(result.Output.Split('\n'), line =>
            line.Contains(StrataLint.Scribe.CanonicalValuesWriter.RelativePath, StringComparison.Ordinal));
    }

    [Fact]
    public void ExistingCoverageRequiresCurrentStatementBinding()
    {
        using var world = new BatchWorld();
        Assert.True(world.Run(Row(First, Gid)).Success);
        world.Rewrite(entry => entry.AtomId == First
            ? entry with { Coverage = [new DigestionCoverageEdge(Gid, "sha256:" + new string('f', 64))] }
            : entry);

        var result = world.Run(Row(First, Gid));

        Assert.Equal(1, result.ExitCode);
        Assert.Equal("failed", Assert.Single(Results(result)).Status);
    }

    [Fact]
    public void IndependentUnrequestedLedgerBytesRemainUnchanged()
    {
        using var world = new BatchWorld();
        var path = world.LedgerPaths().Single(path => path.EndsWith(Second + ".yaml", StringComparison.Ordinal));
        File.AppendAllText(path, "# preserved unrelated annotation\n");
        var before = TemporaryFileSystem.File.ReadAllBytes(path);

        var result = world.Run(Row(First, Gid));

        Assert.True(result.Success, result.Error + result.Output);
        Assert.Equal(before, TemporaryFileSystem.File.ReadAllBytes(path));
    }

    private const string Gid = "D5/S0/Carrier/Probe.probe";
    private const string OtherGid = "D5/S0/Carrier/Probe.other";
    private const string MissingGid = "D5/S0/Carrier/Probe.missing";
    private static string First => CoverWorld.DefaultAtomId;
    private static string Second => CoverWorld.OtherAtomId;
    private static string Row(string atom, string gid) => atom + "\t" + gid + "\n";

    private sealed record BatchResult(string AtomId, string Status, int[] Lines, string Reason);

    private static BatchResult[] Results(CommandResult result) => result.Output.Split('\n')
        .Where(line => line.StartsWith("COVER_BATCH ", StringComparison.Ordinal))
        .Select(line =>
        {
            using var json = JsonDocument.Parse(line["COVER_BATCH ".Length..]);
            var root = json.RootElement;
            return new BatchResult(root.GetProperty("atom_id").GetString()!, root.GetProperty("status").GetString()!,
                root.GetProperty("lines").EnumerateArray().Select(item => item.GetInt32()).ToArray(),
                root.GetProperty("reason").GetString()!);
        }).ToArray();

    private sealed class BatchWorld : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        private readonly CoverInputs inputs;
        internal string Root { get; }
        internal FakeRepositoryGateway Repository { get; }
        internal FakeLeanReportSource Report { get; }
        internal bool UseGitReader { get; init; }
        internal string? ParentId { get; }
        internal ImmutableArray<string> ChildIds { get; } = [];

        internal BatchWorld(Func<DigestionLedgerEntry, DigestionLedgerEntry>? edit = null, bool chain = false)
        {
            Root = Path.Combine(temporary.Path, "repo");
            inputs = new CoverSpec { OtherAtomGid = Gid, ReportDeclarations = ["probe", "other"] }.Materialize();
            var document = inputs.Document.WithDigestionSources(inputs.Document.RequireDigestionSources()
                .Select(source => source with
                {
                    Entries = source.Entries.Select(entry =>
                    {
                        var open = entry with
                        {
                            Coverage = [],
                            ProjectedStatus = new(DigestionMigrationState.Residual, DigestionTruthState.Open),
                        };
                        return edit?.Invoke(open) ?? open;
                    }).ToImmutableArray(),
                }).ToImmutableArray());
            if (chain)
            {
                var sourceText = "# PZG\n\n**\u5b9a\u7406 18.7(Historical)**. first historical clause.\n\n"
                    + "**\u63a8\u8bba:Historical second clause**. second historical clause.\n\n";
                var atomized = PzgAtomizer.Atomize(Encoding.UTF8.GetBytes(sourceText), DigestionTestSupport.Rules);
                var parent = Assert.Single(atomized.Claims);
                var children = Assert.Single(atomized.ClausePlans).Children;
                ParentId = parent.Fingerprints.RawSha256["sha256:".Length..];
                ChildIds = children.Select(child => child.Fingerprints.RawSha256["sha256:".Length..]).ToImmutableArray();
                var source = document.RequireDigestionSources()[0];
                var parentEntry = source.Entries[0] with
                {
                    Atomizer = AtomizerRegistry.PzgId,
                    AtomId = ParentId,
                    Fingerprints = parent.Fingerprints,
                    CasRef = parent.Fingerprints.RawSha256,
                    Coverage = inputs.Document.RequireDigestionEntries().Single(entry => entry.AtomId == Second).Coverage,
                    ProjectedStatus = new(DigestionMigrationState.Partial, DigestionTruthState.Closed),
                    Receipts = new([], ChildIds, null),
                };
                var childEntries = children.Select((child, index) => parentEntry with
                {
                    AtomId = ChildIds[index],
                    Fingerprints = child.Fingerprints,
                    CasRef = child.Fingerprints.RawSha256,
                    Coverage = [],
                    Receipts = new([], [], null),
                    ProjectedStatus = new(DigestionMigrationState.Residual, DigestionTruthState.Open),
                });
                document = document.WithDigestionSources([source with
                {
                    Atomizer = AtomizerRegistry.PzgId,
                    Entries = [parentEntry, .. childEntries],
                }]);
                inputs.Files[source.SourcePath] = sourceText;
                foreach (var atom in children.Prepend(parent))
                {
                    var cas = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
                    inputs.Files[cas.RelativePath] = Encoding.UTF8.GetString(cas.Bytes.AsSpan());
                }
            }
            DirectoryLedgerTestSupport.ReplaceWithProjection(inputs.Files, document);
            inputs.Files[TheoryAtomizerDataLoader.DataPath] = Encoding.UTF8.GetString(DigestionTestSupport.RulesBytes);
            foreach (var (path, contents) in inputs.Files)
            {
                var fullPath = Path.Combine(Root, path);
                Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
                File.WriteAllText(fullPath, contents);
            }
            ProducerInputFixture.CopyBatchProducerInputs(Root);
            WriteValuesInputs(Root);
            Repository = new FakeRepositoryGateway(RawChangeSet.Create([]), null, null,
                currentReader: () => UseGitReader ? GitRepositorySnapshotReader.ReadCurrent(Root) : ReadFiles());
            var reports = inputs.Report.Files.ToDictionary(pair => pair.Key.Value, pair => pair.Value,
                StringComparer.Ordinal);
            foreach (var path in Directory.EnumerateFiles(Root, "*.lean", SearchOption.AllDirectories)
                .Select(path => Path.GetRelativePath(Root, path).Replace('\\', '/'))
                .Where(LeanClosureValidator.IsReportLean))
                reports.TryAdd(path, new LeanFileReport([], []));
            Report = new FakeLeanReportSource(LeanAxiomReport.Create(reports));
        }

        internal CommandResult Run(string input)
        {
            var path = Path.Combine(temporary.Path, "atoms.tsv");
            File.WriteAllText(path, input);
            return CoverBatchCommand.Run(Root, Repository, Report,
                CoverWorld.FixtureUtc, ["--atoms", path]);
        }

        internal void RunSingles()
        {
            foreach (var (atom, gid) in new[] { (First, Gid), (Second, OtherGid) })
            {
                var result = CoverAtomCommand.Run(Root, Repository, Report, CoverWorld.FixtureUtc,
                    ["--cover-atom", atom, "--gid", gid]);
                Assert.True(result.Success, result.Error);
            }
        }

        internal string WriteReportBundle()
        {
            TestGit.Run(Root, "init", "--quiet");
            TestGit.Run(Root, "add", ".");
            TestGit.Run(Root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.test",
                "commit", "--quiet", "-m", "synthetic producer inputs");
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(Repository.ReadCurrent())).Snapshot;
            var reports = inputs.Report.Files.ToDictionary(pair => pair.Key.Value, pair => pair.Value, StringComparer.Ordinal);
            foreach (var path in snapshot.Files.Keys.Where(path => LeanClosureValidator.IsManagedLean(path.Value)))
                reports.TryAdd(path.Value, new LeanFileReport([], []));
            var reportPath = RawLeanReportArtifact.DefaultPath(Root);
            RawLeanReportArtifact.WriteFile(reportPath, snapshot, LeanAxiomReport.Create(reports));
            ProducerInputFixture.AttestBatchReport(Root, reportPath);
            return reportPath;
        }

        internal CommandResult RunProducers(string input)
        {
            var path = Path.Combine(temporary.Path, "atoms.tsv");
            TemporaryFileSystem.File.WriteAllText(path, input);
            return CoverBatchCommand.Run(Root, Repository, new PrecomputedLeanReportSource(Root),
                CoverWorld.FixtureUtc, ["--atoms", path]);
        }

        private RawRepositorySnapshot ReadFiles() => RawRepositorySnapshot.Create(
            Directory.EnumerateFiles(Root, "*", SearchOption.AllDirectories)
                .Select(path => new RawRepositoryEntry(Path.GetRelativePath(Root, path).Replace('\\', '/'),
                    ImmutableArray.CreateRange(File.ReadAllBytes(path)))));

        internal DigestionLedgerEntry Entry(string atomId) => BackfillInventoryLoader.LoadRoot(Root)
            .RequireDigestionEntries().Single(entry => entry.AtomId == atomId);
        internal string LedgerImage() => DirectoryLedgerTestSupport.Image(Root);
        internal string[] LedgerPaths() => Directory.GetFiles(Path.Combine(Root, BackfillInventoryLoader.RootPath),
            "*.yaml", SearchOption.AllDirectories);
        internal void Rewrite(Func<DigestionLedgerEntry, DigestionLedgerEntry> edit)
        {
            var document = BackfillInventoryLoader.LoadRoot(Root);
            var files = new Dictionary<string, string>(StringComparer.Ordinal);
            DirectoryLedgerTestSupport.ReplaceWithProjection(files, document.WithDigestionSources(
                document.RequireDigestionSources().Select(source => source with
                {
                    Entries = source.Entries.Select(edit).ToImmutableArray(),
                }).ToImmutableArray()));
            DirectoryLedgerTestSupport.Write(Root, files);
        }
        public void Dispose() => temporary.Dispose();
    }

    private sealed class CallbackVerifier(Action callback) : IScribeEmissionVerifier
    {
        public VerifiedScribeEmissions Verify(RepositorySnapshot snapshot, LeanAxiomReport report,
            RawChangeSet? changes, FrozenStateCatalog? frozenState = null,
            FrozenStatementIndex? frozenStatements = null)
        {
            callback();
            return VerifiedScribeEmissions.Empty;
        }
    }
}
