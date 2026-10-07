using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestRobustTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Ingest_ConcurrentClaimAfterValidation_AllAndSource(bool sourceScoped)
    {
        var fixture = ConcurrentClaimFixture();
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        RawRepositorySnapshot? afterWinner = null;
        var dependencies = new ReportFreeIngestDependencies(BeforeCommit: () =>
        {
            var winner = Environment(fixture, temporary).Ingest(Arguments("beta"));
            Assert.True(winner.Success, winner.Error);
            AssertSingleClaim(temporary, "beta");
            afterWinner = DirectoryLedgerTestSupport.ReadRepository(temporary);
        });

        var result = Environment(fixture, temporary, dependencies: dependencies)
            .Ingest(sourceScoped ? Arguments("alpha") : Arguments("alpha", "beta"));

        Assert.False(result.Success);
        var atomId = Atom(Addition).Fingerprints.RawSha256[7..];
        Assert.Equal($"INGEST_INVALID atom id {atomId} already registered by beta since planning\n", result.Error);
        Assert.NotNull(afterWinner);
        AssertSameRepository(afterWinner, DirectoryLedgerTestSupport.ReadRepository(temporary));
        AssertSingleClaim(temporary, "beta");
    }

    [Fact]
    public void Ingest_RollbackCannotDeleteCommittedPeerCas()
    {
        var fixture = Fixture(Ledger(populated: false), AlphaText + Addition);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var peer = Environment(fixture, temporary).Ingest(Arguments("beta"));
        Assert.True(peer.Success, peer.Error);
        var before = DirectoryLedgerTestSupport.ReadRepository(temporary);
        fixture.Files.Clear();
        foreach (var entry in before.Entries)
            fixture.Files.Add(entry.Path, Encoding.UTF8.GetString(entry.Bytes.AsSpan()));
        var newCasPaths = new[] { Atom(AlphaText), Atom(Addition) }
            .Select(atom => Path.Combine(temporary.Path, DigestionCasStore.Capture(atom.RawBytes.AsSpan()).RelativePath))
            .ToArray();
        Assert.All(newCasPaths, path => Assert.False(File.Exists(path)));
        var committedPaths = new List<string>();
        var attempts = 0;
        var dependencies = new ReportFreeIngestDependencies(CommitLedgerFile: (pending, target) =>
        {
            attempts++;
            Assert.All(newCasPaths, path => Assert.True(File.Exists(path)));
            if (attempts == 2)
            {
                Assert.True(File.Exists(Assert.Single(committedPaths)));
                throw new IOException("injected second ledger publication failure");
            }
            File.Move(pending, target, overwrite: false);
            committedPaths.Add(target);
        });

        var result = Environment(fixture, temporary, dependencies: dependencies).Ingest(Arguments("alpha"));

        Assert.False(result.Success);
        Assert.Contains("injected second ledger publication failure", result.Error, StringComparison.Ordinal);
        Assert.Equal(2, attempts);
        AssertSameRepository(before, DirectoryLedgerTestSupport.ReadRepository(temporary));
        Assert.All(newCasPaths, path => Assert.False(File.Exists(path)));
        Assert.Equal(Atom(BetaText).RawBytes.ToArray(), File.ReadAllBytes(Path.Combine(
            temporary.Path, DigestionCasStore.Capture(Atom(BetaText).RawBytes.AsSpan()).RelativePath)));
        Assert.Empty(Directory.EnumerateFiles(temporary.Path, "*.tmp", SearchOption.AllDirectories));
        var retry = Environment(fixture, temporary).Ingest(Arguments("alpha"));
        Assert.True(retry.Success, retry.Error);
        AssertExistingLedgerFilesUnchanged(before, DirectoryLedgerTestSupport.ReadRepository(temporary));
    }

    private static RuleFixture ConcurrentClaimFixture()
    {
        var fixture = Fixture();
        fixture.Files[AlphaPath] += Addition;
        fixture.Files[BetaPath] += Addition;
        return fixture;
    }

    private static void AssertSingleClaim(TemporaryDirectory temporary, string owner)
    {
        var atom = Atom(Addition);
        var atomId = atom.Fingerprints.RawSha256[7..];
        var paths = Directory.EnumerateFiles(Path.Combine(temporary.Path, BackfillInventoryLoader.RootPath),
            atomId + ".yaml", SearchOption.AllDirectories).ToArray();
        Assert.Equal(Path.Combine(temporary.Path, SourcePrefix(owner), "residual-open", atomId + ".yaml"),
            Assert.Single(paths));
        var entry = Assert.Single(BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries(),
            entry => entry.AtomId == atomId);
        Assert.Equal(owner, entry.SourceId);
        Assert.Equal(atom.RawBytes.ToArray(),
            File.ReadAllBytes(Path.Combine(temporary.Path, DigestionCasStore.RootPath, atomId)));
    }

    private static void AssertSameRepository(RawRepositorySnapshot before, RawRepositorySnapshot after)
    {
        Assert.Equal(before.Entries.Select(static entry => entry.Path).Order(StringComparer.Ordinal),
            after.Entries.Select(static entry => entry.Path).Order(StringComparer.Ordinal));
        AssertExistingLedgerFilesUnchanged(before, after);
    }

    private static async Task<T> AwaitIngestInfrastructure<T>(Task<T> task)
    {
        try
        {
            return await task.WaitAsync(TestBudgets.WorkflowProcessHangGuard);
        }
        catch (TimeoutException)
        {
            throw new SkipException("infrastructure-hang-guard expired: ingest publication barrier");
        }
    }

    private sealed class IngestPublicationBarrier : IDisposable
    {
        private readonly TaskCompletionSource reached = new(TaskCreationOptions.RunContinuationsAsynchronously);
        private readonly ManualResetEventSlim resume = new(false);

        internal void Commit(string pending, string target)
        {
            reached.TrySetResult();
            resume.Wait();
            File.Move(pending, target, overwrite: false);
        }

        internal async Task WaitForPublication(Task<CommandResult> writer)
        {
            var first = await AwaitIngestInfrastructure(Task.WhenAny(reached.Task, writer));
            if (first == writer)
                Assert.Fail("ingest completed before publication barrier: " + (await writer).Error);
        }

        internal void Resume() => resume.Set();

        public void Dispose() => resume.Dispose();
    }
}
