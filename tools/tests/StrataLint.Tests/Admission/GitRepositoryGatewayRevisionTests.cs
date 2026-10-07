using System.Text;
using System.Security.Cryptography;
using Trureturing.Truth;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

[CollectionDefinition("Repository snapshot allocation", DisableParallelization = true)]
public sealed class RepositorySnapshotAllocationCollection;

[Collection("Repository snapshot allocation")]
public sealed class GitRepositoryGatewayRevisionTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ProjectionKeepsAllPathsButReadsOnlySelectedBodies(bool historical)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        File.WriteAllText(Path.Combine(repository.Path, "selected.txt"), "selected\n");
        File.WriteAllBytes(Path.Combine(repository.Path, "unrelated.bin"), new byte[2 * 1024 * 1024]);
        TestGit.Run(repository.Path, "add", ".");
        TestGit.Run(repository.Path, "commit", "-m", "projection fixture");
        var gateway = new GitRepositoryGateway(repository.Path);
        var revision = TestGit.Run(repository.Path, "rev-parse", "HEAD").Trim();
        var runner = new CountingBlobGitProcessRunner();
        var recordingGateway = new GitRepositoryGateway(repository.Path, runner, "git");
        var snapshot = historical
            ? recordingGateway.ReadRevisionProjection(revision, static path => path == "selected.txt")
            : gateway.ReadCurrentProjection(static path => path == "selected.txt");

        Assert.Equal(["selected.txt", "unrelated.bin"], snapshot.Entries.Select(static entry => entry.Path).Order(StringComparer.Ordinal));
        AssertEntry(Assert.Single(snapshot.Entries, static entry => entry.Path == "selected.txt"), "selected.txt", "selected\n");
        Assert.Empty(Assert.Single(snapshot.Entries, static entry => entry.Path == "unrelated.bin").Bytes);
        Assert.False(Assert.Single(snapshot.Entries, static entry => entry.Path == "unrelated.bin").ContentWasRead);
        Assert.True(Assert.Single(snapshot.Entries, static entry => entry.Path == "selected.txt").ContentWasRead);
        if (historical)
        {
            Assert.Equal([TestGit.Run(repository.Path, "rev-parse", revision + ":selected.txt").Trim()], runner.BlobsRead);
            Assert.True(runner.BlobOutputBytes < 128);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ProjectionHashesOriginalBytesWithoutRetainingUnselectedBodies(bool historical)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var files = new Dictionary<string, byte[]>
        {
            ["selected.txt"] = Encoding.UTF8.GetBytes("selected\n"),
            ["empty.bin"] = [],
            ["duplicate.txt"] = Encoding.UTF8.GetBytes("selected\n"),
            ["unrelated.bin"] = Enumerable.Repeat((byte)255, 1024 * 1024).ToArray(),
            ["\U00010000.txt"] = [0, 128, 255],
            ["\uE000.txt"] = [10],
        };
        foreach (var (path, body) in files) File.WriteAllBytes(Path.Combine(repository.Path, path), body);
        TestGit.Run(repository.Path, "add", ".");
        TestGit.Run(repository.Path, "commit", "-m", "hash projection fixture");
        var revision = TestGit.Run(repository.Path, "rev-parse", "HEAD").Trim();
        var gateway = new GitRepositoryGateway(repository.Path);
        var hashes = new Dictionary<string, byte[]>(StringComparer.Ordinal);
        void Observe(string path, ReadOnlyMemory<byte> hash) => hashes.Add(path, hash.ToArray());
        var snapshot = historical
            ? gateway.ReadRevisionProjection(revision, static path => path == "selected.txt", Observe)
            : gateway.ReadCurrentProjection(static path => path == "selected.txt", Observe);

        Assert.Equal(files.Count, hashes.Count);
        foreach (var (path, body) in files) Assert.Equal(SHA256.HashData(body), hashes[path]);
        Assert.All(snapshot.Entries.Where(static entry => entry.Path != "selected.txt"), static entry => Assert.Empty(entry.Bytes));
        var old = TruthGraphSnapshotIdentity.Compute(files.Select(pair => new SnapshotDigestEntry(pair.Key, pair.Value, false)));
        var streamed = TruthGraphSnapshotIdentity.ComputeContentHashes(hashes.Select(pair => new SnapshotContentHashEntry(pair.Key, pair.Value, false)));
        Assert.Equal(old, streamed);
    }

    [Fact]
    public void PrehashedSnapshotIdentityMatchesOriginalFramingAndProjectionMarker()
    {
        var files = new[]
        {
            new SnapshotDigestEntry("\uE000", new byte[] { 0, 255 }, false),
            new SnapshotDigestEntry("generated", new byte[] { 123 }, true),
            new SnapshotDigestEntry("\U00010000", ReadOnlyMemory<byte>.Empty, false),
        };
        var hashes = files.Select(file => new SnapshotContentHashEntry(file.Path, SHA256.HashData(file.Content.Span), file.IsGeneratedProjection)).ToArray();
        Assert.Equal("sha256:d79bdde819e6ca1be2d2431fb5266f05b71c598f76aad7185c1aeda4b8409dc1", TruthGraphSnapshotIdentity.Compute(files));
        Assert.Equal(TruthGraphSnapshotIdentity.Compute(files), TruthGraphSnapshotIdentity.ComputeContentHashes(hashes));
        hashes[1] = hashes[1] with { ContentHash = new byte[32] };
        Assert.Equal(TruthGraphSnapshotIdentity.Compute(files), TruthGraphSnapshotIdentity.ComputeContentHashes(hashes));
        hashes[0] = hashes[0] with { ContentHash = new byte[32] };
        Assert.NotEqual(TruthGraphSnapshotIdentity.Compute(files), TruthGraphSnapshotIdentity.ComputeContentHashes(hashes));
        Assert.NotEqual(TruthGraphSnapshotIdentity.Compute(files), TruthGraphSnapshotIdentity.ComputeContentHashes(hashes.Take(2)));
        Assert.NotEqual(TruthGraphSnapshotIdentity.Compute(files), TruthGraphSnapshotIdentity.ComputeContentHashes(hashes.Select(file => file with { Path = file.Path + "/renamed" })));
        Assert.Throws<ArgumentException>(() => TruthGraphSnapshotIdentity.ComputeContentHashes(
            [new SnapshotContentHashEntry("invalid", new byte[31], false)]));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void StreamingHashAllocationDoesNotGrowWithAnUnselectedBody(bool historical)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var payload = Enumerable.Repeat((byte)'x', 16 * 1024 * 1024).ToArray();
        File.WriteAllBytes(Path.Combine(repository.Path, "large.txt"), payload);
        File.WriteAllText(Path.Combine(repository.Path, "selected.txt"), "selected\n");
        TestGit.Run(repository.Path, "add", ".");
        TestGit.Run(repository.Path, "commit", "-m", "allocation fixture");
        var gateway = new GitRepositoryGateway(repository.Path);
        _ = gateway.ReadRevisionProjection("HEAD", static path => path == "selected.txt");
        ReadOnlyMemory<byte> observed = default;
        void Observe(string path, ReadOnlyMemory<byte> hash) { if (path == "large.txt") observed = hash; }
        var before = GC.GetTotalAllocatedBytes(precise: true);
        var snapshot = historical
            ? gateway.ReadRevisionProjection("HEAD", static path => path == "selected.txt", Observe)
            : gateway.ReadCurrentProjection(static path => path == "selected.txt", Observe);
        var allocated = GC.GetTotalAllocatedBytes(precise: true) - before;

        Assert.Equal(SHA256.HashData(payload), observed.ToArray());
        Assert.Empty(Assert.Single(snapshot.Entries, static entry => entry.Path == "large.txt").Bytes);
        Assert.True(allocated < payload.Length / 2, $"Hashing an unselected {payload.Length}-byte body allocated {allocated} bytes.");
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ProjectionFallbackCannotHashAnUnreadPlaceholder(bool historical)
    {
        var raw = RawRepositorySnapshot.Create([new RawRepositoryEntry("unread.txt", [], ContentWasRead: false)]);
        IRepositoryGateway gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), raw, raw);
        Assert.Throws<InvalidOperationException>(() => historical
            ? gateway.ReadRevisionProjection("fixture", static _ => false, static (_, _) => { })
            : gateway.ReadCurrentProjection(static _ => false, static (_, _) => { }));
    }

    [Theory]
    [InlineData("wrong-oid")]
    [InlineData("wrong-type")]
    [InlineData("wrong-size")]
    [InlineData("short-body")]
    [InlineData("missing-newline")]
    [InlineData("trailing-data")]
    [InlineData("oversized-header")]
    public void StreamingRevisionRejectsMalformedBatchFrames(string failure)
    {
        using var repository = new TemporaryDirectory();
        var gateway = new GitRepositoryGateway(repository.Path, new MalformedBatchRunner(failure), "git");
        Assert.Throws<GitInfrastructureException>(() => gateway.ReadRevisionProjection("fixture", static _ => false, static (_, _) => { }));
    }

    private sealed class MalformedBatchRunner(string failure) : IGitProcessRunner
    {
        public ProcessOutput Run(string fileName, IReadOnlyList<string> arguments, string workingDirectory,
            TimeSpan timeout, int maximumOutputBytes = GitRepositoryGateway.DefaultGitOutputBytes,
            ReadOnlyMemory<byte> standardInput = default)
        {
            if (arguments[0] == "ls-tree")
                return new(0, Encoding.UTF8.GetBytes($"100644 blob {FirstOid} 3\tpayload.txt\0"), []);
            var header = failure switch
            {
                "wrong-oid" => SecondOid + " blob 3\n",
                "wrong-type" => FirstOid + " tree 3\n",
                "wrong-size" => FirstOid + " blob 4\n",
                "oversized-header" => new string('x', 257) + "\n",
                _ => FirstOid + " blob 3\n",
            };
            var body = failure switch
            {
                "short-body" => "x",
                "missing-newline" => "xyz!",
                "trailing-data" => "xyz\nextra",
                _ => "xyz\n",
            };
            return new(0, Encoding.UTF8.GetBytes(header + body), []);
        }
    }

    [Fact]
    public void CurrentSnapshotOwnsOnePayloadBufferAndSurvivesDiskReplacement()
    {
        using var repository = new TemporaryDirectory();
        TestGit.Run(repository.Path, "init");
        var path = Path.Combine(repository.Path, "payload.txt");
        File.WriteAllText(path, "warm reader\n");
        _ = GitRepositorySnapshotReader.ReadCurrent(repository.Path);
        var payload = Enumerable.Repeat((byte)'x', 4 * 1024 * 1024).ToArray();
        File.WriteAllBytes(path, payload);

        var before = GC.GetAllocatedBytesForCurrentThread();
        var snapshot = GitRepositorySnapshotReader.ReadCurrent(repository.Path);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        File.WriteAllText(path, "replacement\n");
        var entry = Assert.Single(snapshot.Entries);
        Assert.Equal("payload.txt", entry.Path);
        Assert.Equal(payload, entry.Bytes.ToArray());
        Assert.True(allocated < payload.Length + payload.Length / 2,
            $"Reading one {payload.Length}-byte file allocated {allocated} bytes.");
    }

    [Fact]
    public void CurrentSnapshotVisitsEveryPathInOrderAcrossProbeWindows()
    {
        using var repository = new TemporaryDirectory();
        TestGit.Run(repository.Path, "init");
        var count = GitRepositorySnapshotReader.ProbeWindowPaths + GitRepositorySnapshotReader.ParallelProbeThreshold + 3;
        var expected = Enumerable.Range(0, count).Select(index => $"d{index % 7}/f{index:D5}.txt")
            .Order(StringComparer.Ordinal).ToArray();
        foreach (var path in expected)
        {
            Directory.CreateDirectory(Path.GetDirectoryName(Path.Combine(repository.Path, path))!);
            File.WriteAllText(Path.Combine(repository.Path, path), path + "\n");
        }

        var visited = new List<string>();
        var inventory = GitRepositorySnapshotReader.VisitCurrent(repository.Path, entry =>
        {
            Assert.Equal(entry.Path + "\n", Encoding.UTF8.GetString(entry.Bytes.AsSpan()));
            visited.Add(entry.Path);
        });

        Assert.Equal(expected, visited);
        Assert.Equal(expected, inventory.Select(row => row.Path));
        Assert.Equal(expected, GitRepositorySnapshotReader.ReadCurrent(repository.Path).Entries.Select(entry => entry.Path));
    }

    [SkippableFact]
    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    public void CurrentSnapshotRaisesTheFirstUnreadablePathInPathOrder()
    {
        using var repository = new TemporaryDirectory();
        TestGit.Run(repository.Path, "init");
        var count = GitRepositorySnapshotReader.ParallelProbeThreshold * 3;
        for (var index = 0; index < count; index++)
            File.WriteAllText(Path.Combine(repository.Path, $"f{index:D4}.txt"), "readable\n");
        var first = Path.Combine(repository.Path, $"f{count / 4:D4}.txt");
        var later = Path.Combine(repository.Path, $"f{count - 2:D4}.txt");
        try
        {
            File.SetUnixFileMode(later, UnixFileMode.None);
            File.SetUnixFileMode(first, UnixFileMode.None);
            var unreadable = true;
            try { _ = File.ReadAllBytes(first); unreadable = false; }
            catch (UnauthorizedAccessException) { }
            Skip.IfNot(unreadable, "The test process can read files without permission bits.");

            var failure = Assert.Throws<UnauthorizedAccessException>(() => GitRepositorySnapshotReader.ReadCurrent(repository.Path));
            Assert.Contains(Path.GetFileName(first), failure.Message, StringComparison.Ordinal);
        }
        finally
        {
            File.SetUnixFileMode(first, UnixFileMode.UserRead | UnixFileMode.UserWrite);
            File.SetUnixFileMode(later, UnixFileMode.UserRead | UnixFileMode.UserWrite);
        }
    }

    private const string FirstOid = "1111111111111111111111111111111111111111";
    private const string SecondOid = "2222222222222222222222222222222222222222";

    [Fact]
    public void ReadRevisionBatchesAllBlobReadsIntoOneGitProcess()
    {
        using var repository = new TemporaryDirectory();
        var runner = new RecordingGitProcessRunner();
        var gateway = new GitRepositoryGateway(
            repository.Path,
            runner,
            "git");

        var snapshot = gateway.ReadRevision("synthetic-base");

        Assert.Collection(
            snapshot.Entries,
            entry => AssertEntry(entry, "alpha.txt", "alpha\n"),
            entry => AssertEntry(entry, "duplicate.txt", "alpha\n"),
            entry => AssertEntry(entry, "empty.txt", string.Empty));
        Assert.Collection(
            runner.Calls,
            arguments => Assert.Equal(["ls-tree", "-r", "-l", "-z", "synthetic-base"], arguments),
            arguments => Assert.Equal(["cat-file", "--batch"], arguments));
    }

    [Fact]
    public void ReadRevisionRoundTripsCommittedBlobBytes()
    {
        using var repository = new TemporaryDirectory();
        TestGit.Run(repository.Path, "init");
        TestGit.Run(
            repository.Path,
            "config",
            "user.email",
            "stratalint@example.invalid");
        TestGit.Run(
            repository.Path,
            "config",
            "user.name",
            "StrataLint Tests");
        var binary = new byte[] { 0, 10, 128, 255 };
        File.WriteAllBytes(Path.Combine(repository.Path, "binary.dat"), binary);
        File.WriteAllBytes(Path.Combine(repository.Path, "empty.dat"), []);
        File.WriteAllText(
            Path.Combine(repository.Path, "first.txt"),
            "shared\n",
            new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(repository.Path, "second.txt"),
            "shared\n",
            new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(repository.Path, "script.sh"),
            "#!/bin/sh\nexit 0\n",
            new UTF8Encoding(false));
        TestGit.Run(repository.Path, "add", ".");
        TestGit.Run(repository.Path, "update-index", "--chmod=+x", "script.sh");
        TestGit.Run(repository.Path, "commit", "-m", "batch fixture");
        var revision = TestGit.Run(repository.Path, "rev-parse", "HEAD").Trim();
        File.WriteAllText(
            Path.Combine(repository.Path, "first.txt"),
            "working tree change\n",
            new UTF8Encoding(false));

        var snapshot = new GitRepositoryGateway(repository.Path).ReadRevision(revision);

        var entries = snapshot.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
        Assert.Equal(binary, entries["binary.dat"].Bytes);
        Assert.Empty(entries["empty.dat"].Bytes);
        Assert.Equal(Encoding.UTF8.GetBytes("shared\n"), entries["first.txt"].Bytes);
        Assert.Equal(entries["first.txt"].Bytes, entries["second.txt"].Bytes);
        Assert.Equal(
            Encoding.UTF8.GetBytes("#!/bin/sh\nexit 0\n"),
            entries["script.sh"].Bytes);
    }

    [Fact]
    public void ScopedRevisionReadsOnlySelectedBlobBytesFromTheImmutableRevision()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        const string target = "selected.txt";
        File.WriteAllText(Path.Combine(repository.Path, target), "committed target\n", new UTF8Encoding(false));
        File.WriteAllBytes(Path.Combine(repository.Path, "unrelated.bin"), Enumerable.Repeat((byte)7, 1024 * 1024).ToArray());
        Directory.CreateDirectory(Path.Combine(repository.Path, "Meta"));
        File.WriteAllText(Path.Combine(repository.Path, "Meta/FILEMAP.toml"), "unneeded policy bytes\n", new UTF8Encoding(false));
        TestGit.Run(repository.Path, "add", ".");
        TestGit.Run(repository.Path, "commit", "-m", "scoped revision fixture");
        var revision = TestGit.Run(repository.Path, "rev-parse", "HEAD").Trim();
        var targetOid = TestGit.Run(repository.Path, "rev-parse", revision + ":" + target).Trim();
        File.WriteAllText(Path.Combine(repository.Path, target), "uncommitted replacement\n", new UTF8Encoding(false));
        File.Delete(Path.Combine(repository.Path, "unrelated.bin"));
        var runner = new CountingBlobGitProcessRunner();
        var gateway = new GitRepositoryGateway(repository.Path, runner, "git");

        var snapshot = gateway.ReadRevision(revision, [":(literal)" + target]);

        Assert.Equal([targetOid], runner.BlobsRead);
        var entry = Assert.Single(snapshot.Entries);
        AssertEntry(entry, target, "committed target\n");
        Assert.Equal("git-sha1:" + targetOid, entry.GitBlobOid);
        Assert.True(runner.BlobOutputBytes < 128, $"selected body read returned {runner.BlobOutputBytes} bytes");
    }

    [Fact]
    public void ReadCurrentOmitsDeletedTrackedFileAndIncludesRenamedFile()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        File.WriteAllText(Path.Combine(repository.Path, "old.txt"), "retained bytes\n");
        File.WriteAllText(Path.Combine(repository.Path, "deleted.txt"), "deleted bytes\n");
        TestGit.Run(repository.Path, "add", ".");
        TestGit.Run(repository.Path, "commit", "-m", "snapshot fixture");
        File.Move(Path.Combine(repository.Path, "old.txt"), Path.Combine(repository.Path, "new.txt"));
        File.Delete(Path.Combine(repository.Path, "deleted.txt"));

        var snapshot = new GitRepositoryGateway(repository.Path).ReadCurrent();

        AssertEntry(Assert.Single(snapshot.Entries), "new.txt", "retained bytes\n");
    }

    [Fact]
    public void ReadCurrentChangesReportsOnlyWorkingTreeDeltaFromHead()
    {
        using var repository = new TemporaryDirectory();
        TestGit.Run(repository.Path, "init");
        TestGit.Run(repository.Path, "config", "user.email", "stratalint@example.invalid");
        TestGit.Run(repository.Path, "config", "user.name", "StrataLint Tests");
        File.WriteAllText(Path.Combine(repository.Path, "tracked.txt"), "baseline\n", new UTF8Encoding(false));
        TestGit.Run(repository.Path, "add", "tracked.txt");
        TestGit.Run(repository.Path, "commit", "-m", "working changes fixture");
        var gateway = new GitRepositoryGateway(repository.Path);

        Assert.Empty(gateway.ReadCurrentChanges().Entries);

        File.WriteAllText(Path.Combine(repository.Path, "tracked.txt"), "changed\n", new UTF8Encoding(false));
        File.WriteAllText(Path.Combine(repository.Path, "untracked.txt"), "new\n", new UTF8Encoding(false));

        Assert.Equal(
            new[]
            {
                ("tracked.txt", RawChangeKind.Modified),
                ("untracked.txt", RawChangeKind.Added),
            },
            gateway.ReadCurrentChanges().Entries
                .Select(static change => (change.Path.Value, change.Kind)));
    }

    [Fact]
    public void PrepareOnDirtyTreeStillRequiresExplicitBase()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        File.WriteAllText(
            Path.Combine(repository.Path, "tracked.txt"),
            "baseline\n",
            new UTF8Encoding(false));
        TestGit.Run(repository.Path, "add", "tracked.txt");
        TestGit.Run(repository.Path, "commit", "-m", "baseline");
        var head = TestGit.Run(repository.Path, "rev-parse", "HEAD").Trim();
        File.WriteAllText(
            Path.Combine(repository.Path, "tracked.txt"),
            "changed\n",
            new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(repository.Path, "untracked.txt"),
            "new\n",
            new UTF8Encoding(false));

        Assert.Throws<InvalidOperationException>(() => new GitRepositoryGateway(repository.Path).Prepare(null));
    }

    [Fact]
    public void PrepareOnCleanTreeWithoutProtectedBaseRequiresProtectedBase()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        File.WriteAllText(
            Path.Combine(repository.Path, "tracked.txt"),
            "baseline\n",
            new UTF8Encoding(false));
        TestGit.Run(repository.Path, "add", "tracked.txt");
        TestGit.Run(repository.Path, "commit", "-m", "baseline");

        var exception = Assert.Throws<InvalidOperationException>(
            () => new GitRepositoryGateway(repository.Path).Prepare(null));

        Assert.Contains("40-hex", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void PrepareUsesAncestorProtectedBaseForChanges()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        File.WriteAllText(
            Path.Combine(repository.Path, "tracked.txt"),
            "baseline\n",
            new UTF8Encoding(false));
        TestGit.Run(repository.Path, "add", "tracked.txt");
        TestGit.Run(repository.Path, "commit", "-m", "baseline");
        var baseline = TestGit.Run(repository.Path, "rev-parse", "HEAD").Trim();
        File.WriteAllText(
            Path.Combine(repository.Path, "tracked.txt"),
            "candidate\n",
            new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(repository.Path, "added.txt"),
            "added\n",
            new UTF8Encoding(false));
        TestGit.Run(repository.Path, "add", ".");
        TestGit.Run(repository.Path, "commit", "-m", "candidate");

        var prepared = new GitRepositoryGateway(repository.Path).Prepare(baseline);

        Assert.Equal(baseline, prepared.Revision);
        Assert.Equal(
            new[]
            {
                ("added.txt", RawChangeKind.Added),
                ("tracked.txt", RawChangeKind.Modified),
            },
            prepared.Changes.Entries.Select(static change =>
                (change.Path.Value, change.Kind)));
    }

    [Fact]
    public void PrepareComparesDivergentBaseAsData()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        File.WriteAllText(
            Path.Combine(repository.Path, "root.txt"),
            "root\n",
            new UTF8Encoding(false));
        TestGit.Run(repository.Path, "add", "root.txt");
        TestGit.Run(repository.Path, "commit", "-m", "root");
        var root = TestGit.Run(repository.Path, "rev-parse", "HEAD").Trim();
        File.WriteAllText(
            Path.Combine(repository.Path, "candidate.txt"),
            "candidate\n",
            new UTF8Encoding(false));
        TestGit.Run(repository.Path, "add", "candidate.txt");
        TestGit.Run(repository.Path, "commit", "-m", "candidate");
        TestGit.Run(repository.Path, "branch", "candidate");
        TestGit.Run(repository.Path, "checkout", "-b", "sibling", root);
        File.WriteAllText(
            Path.Combine(repository.Path, "sibling.txt"),
            "sibling\n",
            new UTF8Encoding(false));
        TestGit.Run(repository.Path, "add", "sibling.txt");
        TestGit.Run(repository.Path, "commit", "-m", "sibling");
        var sibling = TestGit.Run(repository.Path, "rev-parse", "HEAD").Trim();
        TestGit.Run(repository.Path, "checkout", "candidate");

        var prepared = new GitRepositoryGateway(repository.Path).Prepare(sibling);
        Assert.Equal(sibling, prepared.Revision);
        Assert.Equal(new[] { ("candidate.txt", RawChangeKind.Added), ("sibling.txt", RawChangeKind.Deleted) },
            prepared.Changes.Entries.Select(change => (change.Path.Value, change.Kind)));
    }

    [Fact]
    public void PreparePrefersModifiedOverCopySourceForTheSamePath()
    {
        using var repository = new TemporaryDirectory();
        var runner = new PrepareGitProcessRunner(
            "M\0source.txt\0C069\0source.txt\0copy.txt\0");
        var gateway = new GitRepositoryGateway(
            repository.Path,
            runner,
            "git");

        var prepared = gateway.Prepare(FirstOid);

        Assert.Equal(2, prepared.Changes.Entries.Length);
        var source = Assert.Single(
            prepared.Changes.Entries,
            change => change.Path.Value == "source.txt");
        Assert.Equal(RawChangeKind.Modified, source.Kind);
        Assert.Contains(prepared.Changes.Entries, change =>
            change.Path.Value == "copy.txt" && change.Kind == RawChangeKind.Added);
    }

    [Fact]
    public void PreparePrefersDeletedOverRenameSourceCollisionForTheSamePath()
    {
        using var repository = new TemporaryDirectory();
        var runner = new PrepareGitProcessRunner(
            "M\0source.txt\0R100\0source.txt\0renamed.txt\0");
        var gateway = new GitRepositoryGateway(
            repository.Path,
            runner,
            "git");

        var prepared = gateway.Prepare(FirstOid);

        Assert.Equal(2, prepared.Changes.Entries.Length);
        var source = Assert.Single(
            prepared.Changes.Entries,
            change => change.Path.Value == "source.txt");
        Assert.Equal(RawChangeKind.Deleted, source.Kind);
        Assert.Contains(prepared.Changes.Entries, change =>
            change.Path.Value == "renamed.txt" && change.Kind == RawChangeKind.Added);
    }

    [Fact]
    public void ReadChangesDropsCopySourcePathsBecauseTheirBytesAreUnchanged()
    {
        using var repository = new TemporaryDirectory();
        var runner = new PrepareGitProcessRunner(
            "C055\0Meta/Digestion/backfill/d-zcoct/source.toml\0"
            + "Meta/Digestion/backfill/quantum-rh/source.toml\0");
        var gateway = new GitRepositoryGateway(repository.Path, runner, "git");

        var changes = gateway.ReadChanges("synthetic-base");

        Assert.Equal(
            new[] { ("Meta/Digestion/backfill/quantum-rh/source.toml", RawChangeKind.Added) },
            changes.Entries.Select(static change => (change.Path.Value, change.Kind)));
    }

    [Fact]
    public void ReadChangesKeepsAModifiedCopySourceAndAddsTheCopy()
    {
        using var repository = new TemporaryDirectory();
        var runner = new PrepareGitProcessRunner(
            "M\0source.txt\0C069\0source.txt\0copy.txt\0");
        var gateway = new GitRepositoryGateway(repository.Path, runner, "git");

        var changes = gateway.ReadChanges("synthetic-base");

        Assert.Equal(
            new[]
            {
                ("copy.txt", RawChangeKind.Added),
                ("source.txt", RawChangeKind.Modified),
            },
            changes.Entries.Select(static change => (change.Path.Value, change.Kind)));
    }

    [Fact]
    public void ReadChangesReportsARenameAsDeleteAndAdd()
    {
        using var repository = new TemporaryDirectory();
        var runner = new PrepareGitProcessRunner("R100\0old.txt\0new.txt\0");
        var gateway = new GitRepositoryGateway(repository.Path, runner, "git");

        var changes = gateway.ReadChanges("synthetic-base");

        Assert.Equal(
            new[]
            {
                ("new.txt", RawChangeKind.Added),
                ("old.txt", RawChangeKind.Deleted),
            },
            changes.Entries.Select(static change => (change.Path.Value, change.Kind)));
    }

    private static void AssertEntry(RawRepositoryEntry entry, string path, string expected)
    {
        Assert.Equal(path, entry.Path);
        Assert.Equal(Encoding.UTF8.GetBytes(expected), entry.Bytes);
    }

    private static void InitializeRepository(string path)
    {
        TestGit.Run(path, "init");
        TestGit.Run(
            path,
            "config",
            "user.email",
            "stratalint@example.invalid");
        TestGit.Run(
            path,
            "config",
            "user.name",
            "StrataLint Tests");
    }

    private sealed class RecordingGitProcessRunner : IGitProcessRunner
    {
        internal List<string[]> Calls { get; } = [];

        public ProcessOutput Run(
            string fileName,
            IReadOnlyList<string> arguments,
            string workingDirectory,
            TimeSpan timeout,
            int maximumOutputBytes = GitRepositoryGateway.DefaultGitOutputBytes,
            ReadOnlyMemory<byte> standardInput = default)
        {
            Calls.Add(arguments.ToArray());
            return arguments[0] switch
            {
                "ls-tree" => Output(
                    $"100644 blob {FirstOid} 6\talpha.txt\0"
                    + $"100644 blob {FirstOid} 6\tduplicate.txt\0"
                    + $"100644 blob {SecondOid} 0\tempty.txt\0"),
                "cat-file" when Encoding.UTF8.GetString(standardInput.Span)
                    == $"{FirstOid}\n{SecondOid}\n" => Output(
                        $"{FirstOid} blob 6\nalpha\n\n"
                        + $"{SecondOid} blob 0\n\n"),
                "show" when arguments[1] == "synthetic-base:alpha.txt" => Output("alpha\n"),
                "show" when arguments[1] == "synthetic-base:duplicate.txt" => Output("alpha\n"),
                "show" when arguments[1] == "synthetic-base:empty.txt" => Output(string.Empty),
                _ => throw new InvalidOperationException("unexpected Git command"),
            };
        }

        private static ProcessOutput Output(string output) =>
            new(0, Encoding.UTF8.GetBytes(output), []);
    }

    internal sealed class CountingBlobGitProcessRunner : IGitProcessRunner
    {
        private readonly ProductionGitProcessRunner production = new();
        internal List<string> BlobsRead { get; } = [];
        internal int BlobOutputBytes { get; private set; }

        public ProcessOutput Run(string fileName, IReadOnlyList<string> arguments, string workingDirectory,
            TimeSpan timeout, int maximumOutputBytes = GitRepositoryGateway.DefaultGitOutputBytes,
            ReadOnlyMemory<byte> standardInput = default)
        {
            var result = production.Run(fileName, arguments, workingDirectory, timeout, maximumOutputBytes, standardInput);
            if (arguments.SequenceEqual(new[] { "cat-file", "--batch" }))
            {
                BlobsRead.AddRange(Encoding.UTF8.GetString(standardInput.Span).Split('\n', StringSplitOptions.RemoveEmptyEntries));
                BlobOutputBytes += result.StandardOutput.Length;
            }
            return result;
        }
    }

    private sealed class PrepareGitProcessRunner(string diffNameStatus) : IGitProcessRunner
    {
        public ProcessOutput Run(
            string fileName,
            IReadOnlyList<string> arguments,
            string workingDirectory,
            TimeSpan timeout,
            int maximumOutputBytes = GitRepositoryGateway.DefaultGitOutputBytes,
            ReadOnlyMemory<byte> standardInput = default) =>
            arguments[0] switch
            {
                "rev-parse" when arguments[1] == "HEAD" => Output(SecondOid + "\n"),
                "status" => Output(string.Empty),
                "rev-parse" when arguments[1] == "--verify" => Output(FirstOid + "\n"),
                "merge-base" when arguments[1] == "--is-ancestor" => Output(string.Empty),
                "diff" => Output(diffNameStatus),
                "ls-files" => Output(string.Empty),
                _ => throw new InvalidOperationException("unexpected Git command"),
            };

        private static ProcessOutput Output(string output) =>
            new(0, Encoding.UTF8.GetBytes(output), []);
    }
}
