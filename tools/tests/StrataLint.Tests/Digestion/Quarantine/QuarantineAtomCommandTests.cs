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
    private static readonly DigestionAtom FixtureAtom = new(
        0,
        1,
        [(byte)'x'],
        new DigestionFingerprints(Digest, Digest),
        []);

    [Fact]
    public void QuarantineRequestRejectsUnknownKeyWithoutWriting()
    {
        using var execution = Execute(
            Request() + "unexpected = \"value\"\n");

        AssertInvalid(execution, "REQUEST_KEYS_INVALID");
    }

    [Fact]
    public void QuarantineRequestRejectsMissingKeyWithoutWriting()
    {
        using var execution = Execute(Request().Replace(
            $"reentry_condition = \"{ReentryCondition}\"\n",
            string.Empty,
            StringComparison.Ordinal));

        AssertInvalid(execution, "REQUEST_KEYS_INVALID");
    }

    [Fact]
    public void QuarantineRequestRejectsUnknownBlockerClassWithoutWriting()
    {
        using var execution = Execute(Request(blockerClass: "unknown-blocker"));

        AssertInvalid(execution, "BLOCKER_CLASS_UNKNOWN");
    }

    [Theory]
    [InlineData("justification")]
    [InlineData("reentry_condition")]
    public void QuarantineRequestRejectsBlankTextWithoutWriting(string field)
    {
        var request = field == "justification"
            ? Request(justification: "   ")
            : Request(reentryCondition: "   ");
        using var execution = Execute(request);

        AssertInvalid(execution, "REQUEST_VALUE_BLANK");
    }

    [Fact]
    public void QuarantineRejectsAbsentAtomWithoutWriting()
    {
        using var execution = Execute(Request(atomId: OtherAtomId));

        AssertInvalid(execution, "ATOM_ABSENT");
    }

    [Fact]
    public void QuarantineRejectsAmbiguousAtomWithoutWriting()
    {
        using var execution = Execute(
            Request(),
            [Source("first", Entry(sourceId: "first")), Source("second", Entry(sourceId: "second"))]);

        AssertInvalid(execution, "ATOM_AMBIGUOUS");
    }

    [Fact]
    public void QuarantineRejectsEntryWithCoverageWithoutWriting()
    {
        using var execution = Execute(
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
        using var execution = Execute(
            Request(),
            [Source("source", Entry(receipts: Receipts(disposition: disposition)))]);

        AssertInvalid(execution, "COVER_DISPOSITION_PRESENT");
    }

    [Fact]
    public void QuarantineRejectsEntryOutsideResidualOpenWithoutWriting()
    {
        using var execution = Execute(
            Request(),
            [Source("source", Entry(migration: DigestionMigrationState.Partial))]);

        AssertInvalid(execution, "NOT_RESIDUAL_OPEN");
    }

    [Fact]
    public void IdenticalQuarantineRerunIsSuccessfulAndByteStable()
    {
        var quarantine = new DigestionQuarantine(Justification, ReentryCondition, BlockerClass);
        using var execution = Execute(
            Request(),
            [Source("source", Entry(receipts: Receipts(quarantine: quarantine)))]);

        Assert.Equal(0, execution.ExitCode);
        Assert.Equal(string.Empty, execution.Console.Error);
        Assert.Contains(
            $"QUARANTINE_WRITTEN atom_id={AtomId} blocker_class={BlockerClass}",
            execution.Console.Output,
            StringComparison.Ordinal);
        Assert.Equal(execution.BeforeImage, execution.AfterImage);
    }

    [Fact]
    public void ConflictingQuarantineFailsWithoutWriting()
    {
        var quarantine = new DigestionQuarantine("different reason", ReentryCondition, BlockerClass);
        using var execution = Execute(
            Request(),
            [Source("source", Entry(receipts: Receipts(quarantine: quarantine)))]);

        AssertInvalid(execution, "QUARANTINE_CONFLICT");
    }

    [Fact]
    public void ReplaceUpdatesAConflictingQuarantineExplicitly()
    {
        var quarantine = new DigestionQuarantine("different reason", ReentryCondition, BlockerClass);
        using var execution = Execute(
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
        using var execution = Execute(
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
        using var execution = Execute(
            Request(),
            arguments: ["quarantine-atom", "--clear", AtomId, "--base", "baseline"]);

        AssertInvalid(execution, "QUARANTINE_ABSENT");
    }

    [Fact]
    public void ValidQuarantineChangesExactlyOneShardAndRoundTrips()
    {
        using var execution = Execute(
            Request(),
            [Source("source", Entry(), Entry(OtherAtomId))]);

        Assert.Equal(0, execution.ExitCode);
        Assert.Equal(string.Empty, execution.Console.Error);
        Assert.Equal(
            [$"{BackfillInventoryLoader.RootPath}source/residual-open/{AtomId}.yaml"],
            ChangedPaths(execution));
        Assert.Equal(["baseline"], execution.Repository.ReadRevisionCalls);
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
        using var execution = Execute(
            Request(),
            writeAtom: static entry => BackfillInventoryWriter.WriteAtom(entry).AddRange(
                Encoding.UTF8.GetBytes("unexpected: value\n")));

        AssertInvalid(execution, "ROUND_TRIP_FAILED");
    }

    [Fact]
    public void CliApplicationDispatchesQuarantineAtom()
    {
        Assert.Contains("quarantine-atom", CliApplication.ImplementedCommands);

        using var execution = Execute(Request(), requestPathIsAbsolute: true);

        Assert.Equal(0, execution.ExitCode);
        Assert.DoesNotContain("UNKNOWN_COMMAND", execution.Console.Error, StringComparison.Ordinal);
    }

    private static void AssertInvalid(QuarantineExecution execution, string reason)
    {
        Assert.NotEqual(0, execution.ExitCode);
        Assert.StartsWith($"QUARANTINE_INVALID {reason}", execution.Console.Error, StringComparison.Ordinal);
        Assert.Equal(string.Empty, execution.Console.Output);
        Assert.Equal(execution.BeforeImage, execution.AfterImage);
    }

    private static BackfillInventoryDocument Load(QuarantineExecution execution) =>
        BackfillInventoryLoader.LoadRoot(execution.RepositoryRoot.Path);

    private static string[] ChangedPaths(QuarantineExecution execution) =>
        execution.BeforeFiles.Keys
            .Union(execution.AfterFiles.Keys, StringComparer.Ordinal)
            .Where(path => !execution.BeforeFiles.TryGetValue(path, out var before)
                || !execution.AfterFiles.TryGetValue(path, out var after)
                || !before.AsSpan().SequenceEqual(after))
            .Order(StringComparer.Ordinal)
            .ToArray();

    private static QuarantineExecution Execute(
        string request,
        ImmutableArray<DigestionLedgerSource> sources = default,
        IReadOnlyList<string>? arguments = null,
        bool requestPathIsAbsolute = false,
        Func<DigestionLedgerEntry, ImmutableArray<byte>>? writeAtom = null)
    {
        if (sources.IsDefault)
        {
            sources = [Source("source", Entry())];
        }

        var repositoryRoot = new TemporaryDirectory();
        var files = LedgerFiles(sources);
        DirectoryLedgerTestSupport.Write(repositoryRoot.Path, files);
        var requestPath = Path.Combine(repositoryRoot.Path, "quarantine-request.toml");
        File.WriteAllText(requestPath, request, new UTF8Encoding(false));
        var beforeFiles = RepositoryFiles(repositoryRoot.Path);
        var beforeImage = DirectoryLedgerTestSupport.RepositoryImage(repositoryRoot);
        var raw = RawRepositorySnapshot.Create(files.Select(static pair =>
            RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), raw, raw);
        var environment = new ProductionCliEnvironment(
            repositoryRoot.Path,
            gateway,
            new FakeLeanReportSource(null));
        var console = new BufferedConsole();
        var effectiveArguments = arguments ??
        [
            "quarantine-atom",
            "--request",
            requestPathIsAbsolute ? requestPath : "quarantine-request.toml",
            "--base",
            "baseline",
        ];

        int exitCode;
        if (writeAtom is null)
        {
            exitCode = CliApplication.Run(effectiveArguments, environment, console);
        }
        else
        {
            var result = QuarantineAtomCommand.Run(
                repositoryRoot.Path,
                gateway,
                effectiveArguments.Skip(1).ToArray(),
                writeAtom);
            console.WriteOutput(result.Output);
            console.WriteError(result.Error);
            exitCode = result.ExitCode ?? (result.Success ? 0 : 2);
        }
        var afterFiles = RepositoryFiles(repositoryRoot.Path);
        var afterImage = DirectoryLedgerTestSupport.RepositoryImage(repositoryRoot);
        return new QuarantineExecution(
            repositoryRoot,
            gateway,
            console,
            exitCode,
            beforeFiles,
            afterFiles,
            beforeImage,
            afterImage);
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

    private static Dictionary<string, byte[]> RepositoryFiles(string repositoryRoot) =>
        Directory.EnumerateFiles(repositoryRoot, "*", SearchOption.AllDirectories)
            .ToDictionary(
                path => Path.GetRelativePath(repositoryRoot, path)
                    .Replace(Path.DirectorySeparatorChar, '/'),
                File.ReadAllBytes,
                StringComparer.Ordinal);

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
        DigestionCoverDisposition? disposition = null) =>
        new([], [], [], null, quarantine, disposition);

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
        TemporaryDirectory RepositoryRoot,
        FakeRepositoryGateway Repository,
        BufferedConsole Console,
        int ExitCode,
        Dictionary<string, byte[]> BeforeFiles,
        Dictionary<string, byte[]> AfterFiles,
        string BeforeImage,
        string AfterImage) : IDisposable
    {
        public void Dispose() => RepositoryRoot.Dispose();
    }
}
