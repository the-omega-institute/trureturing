using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class QuarantineAtomCommandTests
{
    private const string AtomId = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    private const string OtherAtomId = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
    private const string Digest = "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    private const string BlockerClass = "missing-prerequisite";
    private const string Justification = "the prerequisite theorem is not frozen";
    private const string ReentryCondition = "freeze the prerequisite theorem";
    private static readonly ImmutableArray<string> UnresolvedSubitems = ["pending-clause"];
    private static readonly DigestionAtom FixtureAtom = new(
        0,
        1,
        [(byte)'x'],
        new DigestionFingerprints(Digest, Digest),
        []);

    [Fact]
    public void QuarantineRequestRejectsUnknownKeyWithoutWriting()
    {
        var execution = Execute(
            Request() + "unexpected = \"value\"\n");

        AssertInvalid(execution, "REQUEST_KEYS_INVALID");
    }

    [Fact]
    public void QuarantineRequestRejectsMissingKeyWithoutWriting()
    {
        var execution = Execute(Request().Replace(
            $"reentry_condition = \"{ReentryCondition}\"\n",
            string.Empty,
            StringComparison.Ordinal));

        AssertInvalid(execution, "REQUEST_KEYS_INVALID");
    }

    [Fact]
    public void QuarantineRequestRejectsUnknownBlockerClassWithoutWriting()
    {
        var execution = Execute(Request(blockerClass: "unknown-blocker"));

        AssertInvalid(execution, "BLOCKER_CLASS_UNKNOWN");
        Assert.Contains($"atom_id={AtomId}", execution.Console.Error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("justification")]
    [InlineData("reentry_condition")]
    public void QuarantineRequestRejectsBlankTextWithoutWriting(string field)
    {
        var request = field == "justification"
            ? Request(justification: "   ")
            : Request(reentryCondition: "   ");
        var execution = Execute(request);

        AssertInvalid(execution, "REQUEST_VALUE_BLANK");
        Assert.Contains($"atom_id={AtomId}", execution.Console.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void QuarantineRejectsAbsentAtomWithoutWriting()
    {
        var execution = Execute(Request(atomId: OtherAtomId));

        AssertInvalid(execution, "ATOM_ABSENT");
    }

    [Fact]
    public void QuarantineRejectsAmbiguousAtomWithoutWriting()
    {
        var execution = Execute(
            Request(),
            [Source("first", Entry(sourceId: "first")), Source("second", Entry(sourceId: "second"))]);

        AssertInvalid(execution, "ATOM_AMBIGUOUS");
    }

    [Fact]
    public void QuarantineRejectsEntryWithCoverageWithoutWriting()
    {
        var execution = Execute(
            Request(),
            [Source("source", Entry(coverage: [new DigestionCoverageEdge(
                "D5/S0/Carrier/Probe.probe",
                null)]))]);

        AssertInvalid(execution, "COVERAGE_PRESENT");
    }

    [Fact]
    public void QuarantineRejectsEntryWithCoverDispositionWithoutWriting()
    {
        var disposition = new DigestionCoverDisposition(
            new DigestionStatus(DigestionMigrationState.Partial, DigestionTruthState.Closed),
            ["D5/S0/Carrier/Probe.probe"],
            [new DigestionDispositionGap("unresolved-subitem", "remaining theorem clause")]);
        var execution = Execute(
            Request(),
            [Source("source", Entry(receipts: Receipts(disposition: disposition)))]);

        AssertInvalid(execution, "COVER_DISPOSITION_PRESENT");
    }

    [Fact]
    public void QuarantineRejectsEntryOutsideResidualOpenWithoutWriting()
    {
        var execution = Execute(
            Request(),
            [Source("source", Entry(migration: DigestionMigrationState.Partial))]);

        AssertInvalid(execution, "NOT_RESIDUAL_OPEN");
    }

    [Fact]
    public void IdenticalQuarantineRerunIsSuccessfulAndByteStable()
    {
        var quarantine = new DigestionQuarantine(Justification, ReentryCondition, BlockerClass);
        var execution = Execute(
            Request(),
            [Source("source", Entry(receipts: Receipts(quarantine: quarantine)))]);

        Assert.Equal(0, execution.ExitCode);
        Assert.Equal(string.Empty, execution.Console.Error);
        Assert.Contains(
            $"QUARANTINE_WRITTEN atom_id={AtomId} blocker_class={BlockerClass}",
            execution.Console.Output,
            StringComparison.Ordinal);
        Assert.Empty(ChangedPaths(execution));
        Assert.Equal(0, execution.WriteAtomCalls);
        Assert.Equal(0, execution.ApplyCalls);
    }

    [Fact]
    public void ConflictingQuarantineFailsWithoutWriting()
    {
        var quarantine = new DigestionQuarantine("different reason", ReentryCondition, BlockerClass);
        var execution = Execute(
            Request(),
            [Source("source", Entry(receipts: Receipts(quarantine: quarantine)))]);

        AssertInvalid(execution, "QUARANTINE_CONFLICT");
    }

    [Fact]
    public void ReplaceUpdatesAConflictingQuarantineExplicitly()
    {
        var quarantine = new DigestionQuarantine("different reason", ReentryCondition, BlockerClass);
        var execution = Execute(
            Request(),
            [Source("source", Entry(receipts: Receipts(quarantine: quarantine)))],
            ["quarantine-atom", "--request", "quarantine-request.toml", "--base", "baseline", "--replace"]);

        Assert.Equal(0, execution.ExitCode);
        Assert.Equal(string.Empty, execution.Console.Error);
        Assert.Contains(
            $"QUARANTINE_REPLACED atom_id={AtomId} blocker_class={BlockerClass}",
            execution.Console.Output,
            StringComparison.Ordinal);
        Assert.Equal(
            new DigestionQuarantine(Justification, ReentryCondition, BlockerClass),
            Assert.Single(Load(execution).RequireDigestionEntries()).Receipts.Quarantine);
    }

    [Fact]
    public void ClearRemovesTheExistingQuarantineFromOneAtom()
    {
        var quarantine = new DigestionQuarantine(Justification, ReentryCondition, BlockerClass);
        var execution = Execute(
            Request(),
            [Source("source", Entry(receipts: Receipts(quarantine: quarantine)))],
            ["quarantine-atom", "--clear", AtomId, "--base", "baseline"]);

        Assert.Equal(0, execution.ExitCode);
        Assert.Equal(string.Empty, execution.Console.Error);
        Assert.Contains($"QUARANTINE_CLEARED atom_id={AtomId}", execution.Console.Output, StringComparison.Ordinal);
        Assert.Null(Assert.Single(Load(execution).RequireDigestionEntries()).Receipts.Quarantine);
        Assert.Single(ChangedPaths(execution));
    }

    [Fact]
    public void ClearRejectsAtomWithoutQuarantineAndDoesNotWrite()
    {
        var execution = Execute(
            Request(),
            arguments: ["quarantine-atom", "--clear", AtomId, "--base", "baseline"]);

        AssertInvalid(execution, "QUARANTINE_ABSENT");
    }

    [Fact]
    public void SetPreservesNonEmptyUnresolvedSubitemsByteExactly()
    {
        var execution = Execute(
            Request(),
            [Source("source", Entry(receipts: Receipts(unresolvedSubitems: UnresolvedSubitems)))]);

        Assert.Equal(0, execution.ExitCode);
        AssertReceiptCollectionPreservedByteExactly(
            execution,
            new DigestionQuarantine(Justification, ReentryCondition, BlockerClass));
    }

    [Fact]
    public void ReplacePreservesNonEmptyUnresolvedSubitemsByteExactly()
    {
        var quarantine = new DigestionQuarantine("different reason", ReentryCondition, BlockerClass);
        var execution = Execute(
            Request(),
            [Source(
                "source",
                Entry(receipts: Receipts(
                    quarantine: quarantine,
                    unresolvedSubitems: UnresolvedSubitems)))],
            ["quarantine-atom", "--request", "quarantine-request.toml", "--base", "baseline", "--replace"]);

        Assert.Equal(0, execution.ExitCode);
        AssertReceiptCollectionPreservedByteExactly(
            execution,
            new DigestionQuarantine(Justification, ReentryCondition, BlockerClass));
    }

    [Fact]
    public void ClearPreservesNonEmptyUnresolvedSubitemsByteExactly()
    {
        var quarantine = new DigestionQuarantine(Justification, ReentryCondition, BlockerClass);
        var execution = Execute(
            Request(),
            [Source(
                "source",
                Entry(receipts: Receipts(
                    quarantine: quarantine,
                    unresolvedSubitems: UnresolvedSubitems)))],
            ["quarantine-atom", "--clear", AtomId, "--base", "baseline"]);

        Assert.Equal(0, execution.ExitCode);
        AssertReceiptCollectionPreservedByteExactly(execution, null);
    }

    [Fact]
    public void ValidQuarantineChangesExactlyOneShardAndRoundTrips()
    {
        var execution = Execute(
            Request(),
            [Source("source", Entry(), Entry(OtherAtomId))]);

        Assert.Equal(0, execution.ExitCode);
        Assert.Equal(string.Empty, execution.Console.Error);
        Assert.Equal(
            [$"{BackfillInventoryLoader.RootPath}source/residual-open/{AtomId}.yaml"],
            ChangedPaths(execution));
        Assert.Equal(["baseline"], execution.Repository.ReadRevisionCalls);
        Assert.Equal(1, execution.RequestReadCalls);
        Assert.Equal(1, execution.ApplyCalls);
        var entry = Assert.Single(
            Load(execution).RequireDigestionEntries(),
            candidate => candidate.AtomId == AtomId);
        Assert.Equal(
            new DigestionQuarantine(Justification, ReentryCondition, BlockerClass),
            entry.Receipts.Quarantine);
        Assert.Contains(
            $"QUARANTINE_WRITTEN atom_id={AtomId} blocker_class={BlockerClass} "
                + $"path={BackfillInventoryLoader.RootPath}source/residual-open/{AtomId}.yaml\n",
            execution.Console.Output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void QuarantineRejectsWriterOutputThatDoesNotRoundTrip()
    {
        var execution = Execute(
            Request(),
            writeAtom: static entry => BackfillInventoryWriter.WriteAtom(entry).AddRange(
                Encoding.UTF8.GetBytes("unexpected: value\n")));

        AssertInvalid(execution, "ROUND_TRIP_FAILED");
        Assert.Contains($"atom_id={AtomId}", execution.Console.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void CliApplicationDispatchesQuarantineAtom()
    {
        Assert.Contains("quarantine-atom", CliApplication.ImplementedCommands);
        var environment = new QuarantineCliEnvironment();
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["quarantine-atom", "--synthetic-request"],
            environment,
            console);

        Assert.Equal(0, exitCode);
        Assert.Equal(["--synthetic-request"], environment.Arguments);
        Assert.Equal("QUARANTINE_DISPATCHED\n", console.Output);
        Assert.Equal(string.Empty, console.Error);
    }

    private static void AssertInvalid(QuarantineExecution execution, string reason)
    {
        Assert.NotEqual(0, execution.ExitCode);
        Assert.StartsWith($"QUARANTINE_INVALID {reason}", execution.Console.Error, StringComparison.Ordinal);
        Assert.Equal(string.Empty, execution.Console.Output);
        Assert.Empty(ChangedPaths(execution));
        Assert.Equal(0, execution.ApplyCalls);
        if (!string.Equals(reason, "ROUND_TRIP_FAILED", StringComparison.Ordinal))
        {
            Assert.Equal(0, execution.WriteAtomCalls);
        }
    }

    private static void AssertReceiptCollectionPreservedByteExactly(
        QuarantineExecution execution,
        DigestionQuarantine? quarantine)
    {
        var entry = Assert.Single(Load(execution).RequireDigestionEntries());
        Assert.Equal("pending-clause", Assert.Single(entry.Receipts.UnresolvedSubitems));
        Assert.Equal(quarantine, entry.Receipts.Quarantine);
        var expected = BackfillInventoryWriter.WriteAtom(Entry(
            receipts: Receipts(
                quarantine: quarantine,
                unresolvedSubitems: UnresolvedSubitems)));
        var path = $"{BackfillInventoryLoader.RootPath}source/residual-open/{AtomId}.yaml";
        var actual = Assert.Single(execution.After.Entries, entry => entry.Path == path).Bytes;
        Assert.True(expected.AsSpan().SequenceEqual(actual.AsSpan()));
    }

    private static BackfillInventoryDocument Load(QuarantineExecution execution) =>
        BackfillInventoryLoader.Load(
            Assert.IsType<SnapshotDecodeOutcome.Decoded>(
                SnapshotDecoder.Decode(execution.After)).Snapshot);

    private static string[] ChangedPaths(QuarantineExecution execution) =>
        execution.Before.Entries.Select(static entry => entry.Path)
            .Union(execution.After.Entries.Select(static entry => entry.Path), StringComparer.Ordinal)
            .Where(path => !TryGetBytes(execution.Before, path, out var before)
                || !TryGetBytes(execution.After, path, out var after)
                || !before.AsSpan().SequenceEqual(after.AsSpan()))
            .Order(StringComparer.Ordinal)
            .ToArray();

    private static bool TryGetBytes(
        RawRepositorySnapshot snapshot,
        string path,
        out ImmutableArray<byte> bytes)
    {
        var entry = snapshot.Entries.SingleOrDefault(candidate => candidate.Path == path);
        bytes = entry?.Bytes ?? default;
        return entry is not null;
    }

    private static QuarantineExecution Execute(
        string request,
        ImmutableArray<DigestionLedgerSource> sources = default,
        IReadOnlyList<string>? arguments = null,
        Func<DigestionLedgerEntry, ImmutableArray<byte>>? writeAtom = null)
    {
        if (sources.IsDefault)
        {
            sources = [Source("source", Entry())];
        }

        var files = LedgerFiles(sources);
        var before = RawRepositorySnapshot.Create(files.Select(static pair =>
                RawRepositoryEntry.FromText(pair.Key, pair.Value))
            .Append(new RawRepositoryEntry(
                TheoryAtomizerDataLoader.DataPath,
                ImmutableArray.CreateRange(DigestionTestSupport.RulesBytes))));
        var after = before;
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), before, before);
        var effectiveArguments = arguments ??
        [
            "quarantine-atom",
            "--request",
            "quarantine-request.toml",
            "--base",
            "baseline",
        ];

        var writeAtomCalls = 0;
        ImmutableArray<byte> CountedWriteAtom(DigestionLedgerEntry entry)
        {
            writeAtomCalls++;
            return (writeAtom ?? BackfillInventoryWriter.WriteAtom)(entry);
        }

        var requestReadCalls = 0;
        ImmutableArray<byte> ReadRequest(string repositoryRoot, string requestedPath)
        {
            requestReadCalls++;
            Assert.Equal("synthetic-repository", repositoryRoot);
            Assert.Equal("quarantine-request.toml", requestedPath);
            return ImmutableArray.CreateRange(new UTF8Encoding(false, true).GetBytes(request));
        }

        var applyCalls = 0;
        void CaptureUpdate(
            string repositoryRoot,
            RawRepositorySnapshot current,
            ImmutableArray<IngestCommand.LedgerUpdate> updates)
        {
            applyCalls++;
            Assert.Equal("synthetic-repository", repositoryRoot);
            Assert.Same(before, current);
            var update = Assert.Single(updates);
            var bytes = Assert.IsType<ImmutableArray<byte>>(update.Bytes);
            after = RawRepositorySnapshot.Create(current.Entries.Select(entry =>
                entry.Path == update.Path
                    ? new RawRepositoryEntry(entry.Path, bytes, entry.GitBlobOid)
                    : entry));
        }

        var result = QuarantineAtomCommand.Run(
            "synthetic-repository",
            gateway,
            effectiveArguments.Skip(1).ToArray(),
            CountedWriteAtom,
            ReadRequest,
            CaptureUpdate);
        var console = new BufferedConsole();
        console.WriteOutput(result.Output);
        console.WriteError(result.Error);
        return new QuarantineExecution(
            gateway,
            console,
            result.ExitCode ?? (result.Success ? 0 : 2),
            before,
            after,
            writeAtomCalls,
            requestReadCalls,
            applyCalls);
    }

    private static Dictionary<string, string> LedgerFiles(
        ImmutableArray<DigestionLedgerSource> sources)
    {
        var result = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var source in sources)
        {
            result[$"{BackfillInventoryLoader.RootPath}{source.SourceId}/source.toml"] =
                Encoding.UTF8.GetString(BackfillInventoryWriter.WriteSourceMetadata(source).AsSpan());
            foreach (var entry in source.Entries)
            {
                var state = DigestionStatusNames.Migration(entry.ProjectedStatus.Migration)
                    + "-"
                    + DigestionStatusNames.Truth(entry.ProjectedStatus.Truth);
                result[$"{BackfillInventoryLoader.RootPath}{source.SourceId}/{state}/{entry.AtomId}.yaml"] =
                    Encoding.UTF8.GetString(BackfillInventoryWriter.WriteAtom(entry).AsSpan());
            }
        }

        return result;
    }

    private static DigestionLedgerSource Source(
        string sourceId,
        params DigestionLedgerEntry[] entries) =>
        Assert.Single(DigestionTestSupport.Document(
            AtomizerRegistry.NoAtomizerId,
            [.. entries],
            sourceId,
            $"docs/{sourceId}.md").RequireDigestionSources());

    private static DigestionLedgerEntry Entry(
        string atomId = AtomId,
        string sourceId = "source",
        DigestionMigrationState migration = DigestionMigrationState.Residual,
        DigestionTruthState truth = DigestionTruthState.Open,
        ImmutableArray<DigestionCoverageEdge> coverage = default,
        DigestionReceipts? receipts = null) => DigestionTestSupport.Entry(
            FixtureAtom,
            atomId,
            AtomizerRegistry.NoAtomizerId,
            migration,
            truth,
            coverage.IsDefault
                ? []
                : coverage.Select(static edge => edge.Gid).ToImmutableArray(),
            receipts ?? Receipts(),
            sourceId,
            $"docs/{sourceId}.md",
            Digest);

    private static DigestionReceipts Receipts(
        DigestionQuarantine? quarantine = null,
        DigestionCoverDisposition? disposition = null,
        ImmutableArray<string> unresolvedSubitems = default) =>
        new(
            [],
            unresolvedSubitems.IsDefault ? [] : unresolvedSubitems,
            [],
            null,
            quarantine,
            disposition);

    private static string Request(
        string atomId = AtomId,
        string blockerClass = BlockerClass,
        string justification = Justification,
        string reentryCondition = ReentryCondition) =>
        $"atom_id = \"{atomId}\"\n"
        + $"blocker_class = \"{blockerClass}\"\n"
        + $"justification = \"{justification}\"\n"
        + $"reentry_condition = \"{reentryCondition}\"\n";

    private sealed record QuarantineExecution(
        FakeRepositoryGateway Repository,
        BufferedConsole Console,
        int ExitCode,
        RawRepositorySnapshot Before,
        RawRepositorySnapshot After,
        int WriteAtomCalls,
        int RequestReadCalls,
        int ApplyCalls);

    private sealed class QuarantineCliEnvironment : ICliEnvironment
    {
        public CommandResult DecomposeAtom(IReadOnlyList<string> arguments) => throw new NotSupportedException();
        internal IReadOnlyList<string> Arguments { get; private set; } = [];

        public CommandResult QuarantineAtom(IReadOnlyList<string> arguments)
        {
            Arguments = arguments.ToArray();
            return new CommandResult(true, "QUARANTINE_DISPATCHED\n", string.Empty);
        }

        public ExplicitCommandResult CapacityAudit(IReadOnlyList<string> arguments) => throw Unsupported();
        public AdmissionOutcome Check(IReadOnlyList<string> arguments) => throw Unsupported();
        public AdmissionTopologyOutcome Topology(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult Coverage(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult DigestStatus(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult ShowAtom(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult AtomContext(IReadOnlyList<string> arguments) => throw Unsupported();
        public ExplicitCommandResult EchoVerify(IReadOnlyList<string> arguments) => throw Unsupported();
        public ExplicitCommandResult GateAuthority(IReadOnlyList<string> arguments) => throw Unsupported();
        public ExplicitCommandResult FileMapConform(IReadOnlyList<string> arguments) => throw Unsupported();
        public ExplicitCommandResult DepositHeaderCheck(IReadOnlyList<string> arguments) => throw Unsupported();
        public ExplicitCommandResult LedgerFrozen(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult Ingest(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult AlignDigestionStatus(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult CoverAtom(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult AlignScribeReceipt(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult Route(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult SelfTest(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult RenderDag(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult AlignLedger(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult AppendLedger(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult RevokeLedger(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult ReanchorMathlibLedger(IReadOnlyList<string> arguments) => throw Unsupported();
        public ExplicitCommandResult TruthExport(IReadOnlyList<string> arguments) => throw Unsupported();
        public ExplicitCommandResult TruthRelease(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult CleanLanes(IReadOnlyList<string> arguments) => throw Unsupported();
        public CommandResult Worktree(IReadOnlyList<string> arguments) => throw Unsupported();

        private static NotSupportedException Unsupported() => new();
    }
}
