using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestRobustTests
{
    [Fact]
    public void Ingest_IncompleteLedgerRollbackKeepsReferencedCas()
    {
        if (OperatingSystem.IsWindows())
            throw new SkipException("infrastructure-unavailable: Unix directory permission fault requires Unix");
        var fixture = Fixture(Ledger(populated: false), AlphaText + Addition);
        using var temporary = new TemporaryDirectory();
        RequireEffectiveDirectoryWriteDenial(temporary);
        WriteFixture(temporary, fixture);
        using var gitDirectory = DirectoryLedgerTestSupport.UseGitDirectoryPointer(temporary);
        string? committed = null;
        string? deniedDirectory = null;
        UnixFileMode originalMode = default;
        var attempts = 0;
        var dependencies = new ReportFreeIngestDependencies(CommitLedgerFile: (pending, target) =>
        {
            if (OperatingSystem.IsWindows())
                throw new InvalidOperationException("Unix filesystem fault reproduction requires Unix");
            if (++attempts == 1)
            {
                File.Move(pending, target, overwrite: false);
                committed = target;
                return;
            }
            deniedDirectory = Path.GetDirectoryName(committed!)!;
            originalMode = File.GetUnixFileMode(deniedDirectory);
            File.SetUnixFileMode(deniedDirectory, UnixFileMode.UserRead | UnixFileMode.UserExecute);
            throw new IOException("injected publication failure after first committed atom");
        });
        CommandResult result;
        try
        {
            result = Environment(fixture, temporary, dependencies: dependencies).Ingest(Arguments("alpha"));
        }
        finally
        {
            if (deniedDirectory is not null)
                File.SetUnixFileMode(deniedDirectory, originalMode);
        }
        Assert.False(result.Success);
        Assert.Contains("rollback was incomplete", result.Error, StringComparison.Ordinal);
        Assert.NotNull(committed);
        Assert.True(File.Exists(committed));
        var atomId = Path.GetFileNameWithoutExtension(committed);
        Assert.True(File.Exists(Path.Combine(temporary.Path, DigestionCasStore.RootPath, atomId)),
            "A surviving canonical atom entry must retain its CAS bytes after rollback failure.");
    }

    private static void RequireEffectiveDirectoryWriteDenial(TemporaryDirectory temporary)
    {
        if (OperatingSystem.IsWindows())
            throw new SkipException("infrastructure-unavailable: Unix directory permissions unsupported");
        var directory = Path.Combine(temporary.Path, "permission-probe");
        Directory.CreateDirectory(directory);
        var path = Path.Combine(directory, "write-probe");
        var original = File.GetUnixFileMode(directory);
        try
        {
            File.SetUnixFileMode(directory, UnixFileMode.UserRead | UnixFileMode.UserExecute);
            try
            {
                File.WriteAllText(path, "probe");
            }
            catch (UnauthorizedAccessException)
            {
                return;
            }
        }
        finally
        {
            File.SetUnixFileMode(directory, original);
            File.Delete(path);
            Directory.Delete(directory);
        }
        throw new SkipException("infrastructure-unavailable: directory write denial is not effective");
    }

    [Fact]
    public void Ingest_CreateOnlyPathCollisionRollsBackOnlyOwnFiles() =>
        AssertCreateFailureRollsBack("collision");

    [Fact]
    public void Ingest_SecondLedgerCreateFailureRollsBackOnlyOwnFiles() =>
        AssertCreateFailureRollsBack("second-atom");

    private static void AssertCreateFailureRollsBack(string fault)
    {
        const string newSourcePath = "docs/develop/theory/AA_NEW.md";
        var document = TwoSourceLedger(Source("alpha", AlphaPath, AlphaText), EmptySource("beta", BetaPath));
        var fixture = Fixture(document);
        fixture.Files[newSourcePath] = Addition;
        var reused = Atom(BetaText);
        AddCas(fixture.Files, reused);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var newCasPath = Path.Combine(temporary.Path, DigestionCasStore.Capture(Atom(Addition).RawBytes.AsSpan()).RelativePath);
        Assert.False(File.Exists(newCasPath));
        var reusedCasPath = Path.Combine(temporary.Path, DigestionCasStore.Capture(reused.RawBytes.AsSpan()).RelativePath);
        var reusedBytes = File.ReadAllBytes(reusedCasPath);
        var newMetadataPath = SourcePrefix("aa-new") + "source.toml";
        string? beforeWrite = null;
        var dependencies = new ReportFreeIngestDependencies(BeforeValidation: plan =>
        {
            Assert.Equal(2, plan.AddedAtomIds.Count);
            Assert.Contains(plan.Document.RequireDigestionSources(), static source => source.SourceId == "aa-new");
            var blocker = Path.Combine(temporary.Path,
                fault == "collision" ? newMetadataPath : SourcePrefix("beta") + "residual-open");
            Directory.CreateDirectory(Path.GetDirectoryName(blocker)!);
            File.WriteAllBytes(blocker, Encoding.UTF8.GetBytes("existing blocker\r\n"));
            beforeWrite = DirectoryLedgerTestSupport.RepositoryImage(temporary);
            return plan;
        });

        var result = Environment(fixture, temporary, dependencies: dependencies)
            .Ingest(Arguments(newSourcePath, "beta"));

        Assert.False(result.Success);
        Assert.Contains("INGEST_INVALID", result.Error, StringComparison.Ordinal);
        Assert.Contains(fault == "collision" ? newMetadataPath : "residual-open", result.Error, StringComparison.Ordinal);
        Assert.NotNull(beforeWrite);
        Assert.Equal(beforeWrite, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        Assert.Equal(reusedBytes, File.ReadAllBytes(reusedCasPath));
        Assert.False(File.Exists(newCasPath));
        Assert.Empty(Directory.EnumerateFiles(temporary.Path, "*.tmp", SearchOption.AllDirectories));
        if (fault == "second-atom") Assert.False(File.Exists(Path.Combine(temporary.Path, newMetadataPath)));
    }

    [Fact]
    public void AlignDigestionStatus_ResidualIdCollisionRemainsFailClosedAfterCleanAlignment()
    {
        var alpha = Source("alpha", AlphaPath, AlphaText);
        var betaAtom = Atom(BetaText);
        var occupiedId = betaAtom.Fingerprints.RawSha256["sha256:".Length..];
        alpha = alpha with { Entries = [Assert.Single(alpha.Entries) with { AtomId = occupiedId }] };
        var document = TwoSourceLedger(alpha, EmptySource("beta", BetaPath));
        var fixture = Fixture(document);
        var snapshot = Decode(Raw(fixture.Files));
        var alignment = DigestionLedgerAligner.Evaluate(document, snapshot, document, DigestionAlignmentMode.Ingest);
        Assert.Empty(alignment.Findings);
        Assert.Equal(occupiedId, Assert.Single(alignment.Residual).SuggestedAtomId);

        var failure = Assert.Throws<FormatException>(() => DigestionIngestor.Plan(document, snapshot, document));

        Assert.Equal($"ingest atom id collision at {occupiedId}", failure.Message);
        var reportFree = ReportFreeDigestionIngestor.Plan(document, snapshot, document,
            sourceIds: System.Collections.Immutable.ImmutableHashSet.Create("beta"));
        Assert.Empty(reportFree.AddedAtomIds);
        Assert.Equal(1, reportFree.SkippedExisting);
    }
}
