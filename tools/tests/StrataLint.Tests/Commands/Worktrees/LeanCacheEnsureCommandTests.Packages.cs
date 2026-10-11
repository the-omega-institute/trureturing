using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class LeanCacheEnsureCommandTests
{
    [Fact]
    public void MatchingStampMissingPackagesRecoversOnlyPackagesAndPreservesProjectAndRunnerArtifacts()
    {
        using var fixture = new MissingPackagesFixture();
        var cloner = new RecordingDirectoryCloner
        {
            AfterClone = (_, _) =>
            {
                using var targetWriter = LeanCacheWriterGuard.TryAcquire(fixture.Lake);
                using var donorWriter = LeanCacheWriterGuard.TryAcquire(fixture.DonorLake);
                Assert.Null(targetWriter);
                Assert.Null(donorWriter);
                Assert.False(Directory.Exists(fixture.Packages));
            },
        };
        var runner = new RecordingWorktreeProcessRunner();

        var result = fixture.Ensure(runner, cloner);

        Assert.True(result.Success, result.Error);
        var clone = Assert.Single(cloner.Invocations);
        Assert.Equal(fixture.DonorPackages, clone.Source);
        Assert.StartsWith(Path.Combine(fixture.Lake, "packages.stage-"), clone.Target, StringComparison.Ordinal);
        fixture.AssertPreserved();
        Assert.True(LeanCacheFixtureFile.MathlibProjectionExists(fixture.Target));
        Assert.True(LeanCacheStamp.Matches(fixture.Lake, ReadPins(fixture.Target), out _));
        Assert.Empty(Directory.EnumerateDirectories(fixture.Lake, "*.stage-*"));
        AssertNoCacheGet(runner);
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("seeded", receipt.RootElement.GetProperty("status").GetString());
        Assert.Equal("clonefile", receipt.RootElement.GetProperty("method").GetString());
        Assert.Equal("warm", receipt.RootElement.GetProperty("mathlib_olean_state").GetString());
        Assert.Equal("warm", receipt.RootElement.GetProperty("project_olean_state").GetString());
        Assert.Equal(1, receipt.RootElement.GetProperty("clonefile_attempts").GetInt32());

        var repeated = fixture.Ensure(runner, cloner);

        Assert.True(repeated.Success, repeated.Error);
        Assert.Single(cloner.Invocations);
        fixture.AssertPreserved();
        using var repeatedReceipt = ParseReceipt(repeated.Output);
        Assert.Equal("present", repeatedReceipt.RootElement.GetProperty("status").GetString());
    }

    [Fact]
    public void MatchingStampMissingPackagesWithFailedProjectProbeRefusesWriterWithoutCloning()
    {
        using var fixture = new MissingPackagesFixture(projectProbeFailure: true);
        var probe = FileSystemLeanCacheStateProbe.Instance;
        var project = probe.ProbeOleans(Path.Combine(fixture.Lake, "build", "lib", "lean"));
        Assert.Equal(OleanWarmth.ProbeFailed, project.State);
        Assert.Contains("olean root is not a private directory", project.Error, StringComparison.Ordinal);
        Assert.True(LeanCacheStamp.Matches(fixture.Lake, ReadPins(fixture.Target), out _));
        Assert.False(Path.Exists(fixture.Packages));
        Assert.True(LeanCacheStamp.Matches(fixture.DonorLake, ReadPins(fixture.Repository), out _));
        Assert.True(probe.ProbeOleans(Path.Combine(fixture.DonorLake, "build", "lib", "lean")).IsWarm);
        Assert.True(LeanCacheFixtureFile.MathlibProjectionExists(fixture.Repository));
        var runner = new RecordingWorktreeProcessRunner();
        var cloner = new RecordingDirectoryCloner();

        var result = LeanCacheEnsureCommand.RunWithWriter(
            fixture.Repository,
            ["--path", fixture.Target, "--", "lake", "build"],
            runner,
            cloner,
            probe,
            _ => null);

        Assert.False(result.Success);
        Assert.Contains("COLD_BUILD_REFUSED", result.Error, StringComparison.Ordinal);
        Assert.Contains("cache warmth probe failed", result.Error, StringComparison.Ordinal);
        Assert.Contains(project.Error!, result.Error, StringComparison.Ordinal);
        Assert.Empty(cloner.Invocations);
        Assert.DoesNotContain(runner.Invocations, static call => Path.GetFileName(call.FileName) == "lake");
        AssertNoCacheGet(runner);
        fixture.AssertPreserved();
        Assert.False(Path.Exists(fixture.Packages));
        Assert.Empty(Directory.EnumerateDirectories(fixture.Lake, "*.stage-*"));
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("present", receipt.RootElement.GetProperty("status").GetString());
        Assert.Equal("none", receipt.RootElement.GetProperty("method").GetString());
        Assert.Equal("cold", receipt.RootElement.GetProperty("mathlib_olean_state").GetString());
        Assert.Equal("probe_failed", receipt.RootElement.GetProperty("project_olean_state").GetString());
    }

    [Theory]
    [InlineData("empty")]
    [InlineData("dirty")]
    [InlineData("file")]
    [InlineData("symlink")]
    [InlineData("dangling-symlink")]
    public void MatchingStampExistingPackagesEntryIsNeverReplaced(string kind)
    {
        using var fixture = new MissingPackagesFixture();
        var owned = fixture.CreatePackagesEntry(kind);
        var cloner = new RecordingDirectoryCloner();

        var result = fixture.Ensure(new RecordingWorktreeProcessRunner(), cloner);

        Assert.True(result.Success, result.Error);
        Assert.Empty(cloner.Invocations);
        fixture.AssertPreserved();
        Assert.Equal(owned, fixture.PackagesEntryContents(kind));
        Assert.Empty(Directory.EnumerateDirectories(fixture.Lake, "packages.stage-*"));
    }

    [Theory]
    [InlineData("stamp-mismatch")]
    [InlineData("stamp-missing")]
    [InlineData("project-cold")]
    [InlineData("mathlib-cold")]
    [InlineData("packages-missing")]
    [InlineData("packages-symlink")]
    [InlineData("mathlib-symlink")]
    [InlineData("busy")]
    public void MissingPackagesUnavailableMainDonorFailsClosedWithoutChangingTarget(string failure)
    {
        using var fixture = new MissingPackagesFixture();
        fixture.MakeDonorUnavailable(failure);
        using var busy = failure == "busy" ? LeanCacheGuard.TryAcquireExclusive(fixture.DonorLake) : null;
        if (failure == "busy") Assert.NotNull(busy);
        var runner = new RecordingWorktreeProcessRunner();
        var cloner = new RecordingDirectoryCloner();

        var result = fixture.Ensure(runner, cloner);

        Assert.False(result.Success);
        Assert.Empty(cloner.Invocations);
        fixture.AssertPreserved();
        Assert.False(Directory.Exists(fixture.Packages));
        AssertNoCacheGet(runner);
        using var receipt = ParseReceipt(result.Error);
        Assert.Equal("failed", receipt.RootElement.GetProperty("status").GetString());
        Assert.Equal(0, receipt.RootElement.GetProperty("clonefile_attempts").GetInt32());
        Assert.Contains("warm-donor", receipt.RootElement.GetProperty("reason").GetString(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("stamp-missing")]
    [InlineData("mathlib-cold")]
    [InlineData("packages-symlink")]
    [InlineData("mathlib-symlink")]
    [InlineData("busy")]
    public void MissingPackagesRevalidatesDonorAfterStagingAndDiscardsOnlyItsStage(string failure)
    {
        using var fixture = new MissingPackagesFixture();
        var completed = false;
        var runner = new RecordingWorktreeProcessRunner
        {
            BusyRoot = fixture.Repository,
            BusyWhen = () => completed && failure == "busy",
        };
        var cloner = new RecordingDirectoryCloner
        {
            AfterClone = (_, _) =>
            {
                completed = true;
                if (failure != "busy") fixture.MakeDonorUnavailable(failure);
            },
        };

        var result = fixture.Ensure(runner, cloner);

        Assert.False(result.Success);
        Assert.Single(cloner.Invocations);
        fixture.AssertPreserved();
        Assert.False(Directory.Exists(fixture.Packages));
        Assert.Empty(Directory.EnumerateDirectories(fixture.Lake, "packages.stage-*"));
        AssertNoCacheGet(runner);
        using var receipt = ParseReceipt(result.Error);
        Assert.Equal(1, receipt.RootElement.GetProperty("clonefile_attempts").GetInt32());
    }

    [Theory]
    [InlineData("dirty")]
    [InlineData("file")]
    [InlineData("symlink")]
    [InlineData("dangling-symlink")]
    public void MissingPackagesPublicationRacePreservesCompetingEntry(string kind)
    {
        using var fixture = new MissingPackagesFixture();
        string? owned = null;
        var cloner = new RecordingDirectoryCloner
        {
            AfterClone = (_, _) => owned = fixture.CreatePackagesEntry(kind),
        };

        var result = fixture.Ensure(new RecordingWorktreeProcessRunner(), cloner);

        Assert.False(result.Success);
        Assert.Equal(owned, fixture.PackagesEntryContents(kind));
        fixture.AssertPreserved();
        Assert.Empty(Directory.EnumerateDirectories(fixture.Lake, "packages.stage-*"));
        using var receipt = ParseReceipt(result.Error);
        Assert.Equal(1, receipt.RootElement.GetProperty("clonefile_attempts").GetInt32());
    }

    [Fact]
    public void MissingPackagesChangedTargetStampFailsClosedWithoutRestamping()
    {
        using var fixture = new MissingPackagesFixture();
        var stamp = LeanCacheStamp.PathFor(fixture.Lake);
        var cloner = new RecordingDirectoryCloner
        {
            AfterClone = (_, _) => File.AppendAllText(stamp, " \n"),
        };

        var result = fixture.Ensure(new RecordingWorktreeProcessRunner(), cloner);

        Assert.False(result.Success);
        fixture.AssertPreserved(exceptStamp: true);
        Assert.EndsWith(" \n", File.ReadAllText(stamp), StringComparison.Ordinal);
        Assert.False(Directory.Exists(fixture.Packages));
        Assert.Empty(Directory.EnumerateDirectories(fixture.Lake, "packages.stage-*"));
        Assert.Contains("stamp changed", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void MissingPackagesContentProbeFailureDoesNotReportTheCacheAsPresent()
    {
        using var fixture = new MissingPackagesFixture();
        var probe = new DelegatingLeanCacheStateProbe(
            FileSystemLeanCacheStateProbe.Instance.ProbeOleans,
            path => path == fixture.Packages
                ? new ContentRootInspection(false, "packages probe failed")
                : FileSystemLeanCacheStateProbe.Instance.InspectContentRoot(path));
        var cloner = new RecordingDirectoryCloner();

        var result = LeanCacheEnsureCommand.Run(
            fixture.Repository,
            ["--path", fixture.Target],
            new RecordingWorktreeProcessRunner(),
            cloner,
            removePartial: null,
            probe);

        Assert.False(result.Success);
        Assert.Empty(cloner.Invocations);
        Assert.Contains("packages probe failed", result.Error, StringComparison.Ordinal);
        fixture.AssertPreserved();
    }

    [Fact]
    public void FailedPackagesClonePreservesErrnoAndPreventsWriterEvenWithColdBuildConsent()
    {
        using var fixture = new MissingPackagesFixture();
        var runner = new RecordingWorktreeProcessRunner();
        var cloner = CrossDeviceCloneFailure();

        var result = LeanCacheEnsureCommand.RunWithWriter(
            fixture.Repository,
            ["--path", fixture.Target, "--", "lake", "build"],
            runner,
            cloner,
            FileSystemLeanCacheStateProbe.Instance,
            _ => "1");

        Assert.False(result.Success);
        fixture.AssertPreserved();
        Assert.False(Directory.Exists(fixture.Packages));
        Assert.Empty(Directory.EnumerateDirectories(fixture.Lake, "packages.stage-*"));
        Assert.DoesNotContain(runner.Invocations, static call => Path.GetFileName(call.FileName) == "lake");
        using var receipt = ParseReceipt(result.Error);
        AssertCrossDeviceCloneReceipt(receipt.RootElement);
    }

    [Fact]
    public void InitialBuildSeedWithFailedPackagesCloneKeepsPublishedBuildAndResumesPackagesOnly()
    {
        using var fixture = new MissingPackagesFixture();
        Directory.Delete(Path.Combine(fixture.Lake, "build"), recursive: true);
        File.Delete(LeanCacheStamp.PathFor(fixture.Lake));
        var cloner = new RecordingDirectoryCloner
        {
            Results = new Queue<DirectoryCloneResult>(
            [
                new(true, false, null, 1, null),
                new(false, false, 18, 1, "cross-device clone"),
            ]),
            AfterClone = (_, staged) =>
            {
                if (Path.GetFileName(staged).StartsWith("packages.stage-", StringComparison.Ordinal))
                    Directory.CreateDirectory(staged);
            },
        };
        var runner = new RecordingWorktreeProcessRunner();

        var failed = fixture.Ensure(runner, cloner);

        Assert.False(failed.Success);
        Assert.Equal(2, cloner.Invocations.Count);
        Assert.Equal("warm main build\n", LeanCacheFixtureFile.ReadCacheText(fixture.Target));
        Assert.True(LeanCacheStamp.Matches(fixture.Lake, ReadPins(fixture.Target), out _));
        Assert.Equal("preserved intake\n", File.ReadAllText(Path.Combine(fixture.Lake, "intake", "unique.txt")));
        Assert.False(Directory.Exists(fixture.Packages));
        Assert.Empty(Directory.EnumerateDirectories(fixture.Lake, "*.stage-*"));
        using var failedReceipt = ParseReceipt(failed.Error);
        Assert.Equal(2, failedReceipt.RootElement.GetProperty("clonefile_attempts").GetInt32());
        Assert.Equal(18, failedReceipt.RootElement.GetProperty("clonefile_errno").GetInt32());
        var project = File.ReadAllBytes(Path.Combine(fixture.Lake, "build", "cache.bin"));
        var recoveredCloner = new RecordingDirectoryCloner();

        var recovered = fixture.Ensure(runner, recoveredCloner);

        Assert.True(recovered.Success, recovered.Error);
        Assert.Equal(fixture.DonorPackages, Assert.Single(recoveredCloner.Invocations).Source);
        Assert.Equal(project, File.ReadAllBytes(Path.Combine(fixture.Lake, "build", "cache.bin")));
        Assert.True(LeanCacheFixtureFile.MathlibProjectionExists(fixture.Target));
        AssertNoCacheGet(runner);
    }

    [Theory]
    [InlineData("empty")]
    [InlineData("dirty")]
    public void InitialMissingBuildSeedDoesNotReplaceExistingPackages(string kind)
    {
        using var fixture = new MissingPackagesFixture();
        Directory.Delete(Path.Combine(fixture.Lake, "build"), recursive: true);
        File.Delete(LeanCacheStamp.PathFor(fixture.Lake));
        var owned = fixture.CreatePackagesEntry(kind);
        var cloner = new RecordingDirectoryCloner();

        var result = fixture.Ensure(new RecordingWorktreeProcessRunner(), cloner);

        Assert.True(result.Success, result.Error);
        Assert.EndsWith(Path.Combine(".lake", "build"), Assert.Single(cloner.Invocations).Source, StringComparison.Ordinal);
        Assert.Equal(owned, fixture.PackagesEntryContents(kind));
        Assert.Equal("preserved intake\n", File.ReadAllText(Path.Combine(fixture.Lake, "intake", "unique.txt")));
    }

    [Fact]
    public void InitialBuildSeedKeepsItsCloneReceiptWhenPackagesDonorSelectionThrows()
    {
        using var fixture = new MissingPackagesFixture();
        Directory.Delete(Path.Combine(fixture.Lake, "build"), recursive: true);
        File.Delete(LeanCacheStamp.PathFor(fixture.Lake));
        var donorProject = Path.Combine(fixture.DonorLake, "build", "lib", "lean");
        var probe = new DelegatingLeanCacheStateProbe(
            path => path == donorProject && File.Exists(LeanCacheStamp.PathFor(fixture.Lake))
                ? throw new IOException("packages donor selection probe failed")
                : FileSystemLeanCacheStateProbe.Instance.ProbeOleans(path),
            FileSystemLeanCacheStateProbe.Instance.InspectContentRoot);
        var cloner = new RecordingDirectoryCloner();

        var result = LeanCacheEnsureCommand.Run(
            fixture.Repository, ["--path", fixture.Target],
            new RecordingWorktreeProcessRunner(), cloner, removePartial: null, probe);

        Assert.False(result.Success);
        Assert.Single(cloner.Invocations);
        Assert.Equal("warm main build\n", LeanCacheFixtureFile.ReadCacheText(fixture.Target));
        Assert.False(Directory.Exists(fixture.Packages));
        Assert.Contains("packages donor selection probe failed", result.Error, StringComparison.Ordinal);
        using var receipt = ParseReceipt(result.Error);
        Assert.Equal(1, receipt.RootElement.GetProperty("clonefile_attempts").GetInt32());
    }

    [Fact]
    public void MissingPackagesTransientCloneFailureCleansStageAndAccumulatesRetryReceipt()
    {
        using var fixture = new MissingPackagesFixture();
        var cloner = new RecordingDirectoryCloner
        {
            Results = new Queue<DirectoryCloneResult>(
            [
                new(false, true, 5, 1, "transient clone I/O failure"),
                new(true, false, null, 1, null),
            ]),
            AfterClone = (_, staged) => Directory.CreateDirectory(staged),
        };
        var runner = new RecordingWorktreeProcessRunner();
        using var selection = GitWorktreeInventory.SelectMainDonor(
            GitWorktreeInventory.Locate(fixture.Target, runner),
            ReadPins(fixture.Target),
            runner,
            FileSystemLeanCacheStateProbe.Instance);
        using var writer = LeanCacheWriterGuard.TryAcquire(fixture.Lake);
        Assert.NotNull(writer);
        var waits = new List<TimeSpan>();

        var result = LeanMissingPackagesProvisioner.Provision(
            selection, fixture.Target, ReadPins(fixture.Target), runner,
            writer, cloner, FileSystemLeanCacheStateProbe.Instance, waits.Add);

        Assert.Equal(2, result.Clonefile.Attempts);
        Assert.Equal([5], result.Clonefile.Errnos);
        Assert.Single(waits);
        Assert.Null(result.Clonefile.CleanupError);
        fixture.AssertPreserved();
        Assert.Empty(Directory.EnumerateDirectories(fixture.Lake, "packages.stage-*"));
    }

    [SkippableFact]
    public void MissingPackagesUsesActualNativeClonefileWithoutReplacingProjectLayer()
    {
        Skip.IfNot(OperatingSystem.IsMacOS(), "clonefile requires macOS");
        using var fixture = new MissingPackagesFixture();

        var result = fixture.Ensure(new RecordingWorktreeProcessRunner(), new ApfsDirectoryCloner());

        Assert.True(result.Success, result.Error);
        fixture.AssertPreserved();
        Assert.True(LeanCacheFixtureFile.MathlibProjectionExists(fixture.Target));
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal(1, receipt.RootElement.GetProperty("clonefile_attempts").GetInt32());
    }

    [SkippableFact]
    public void MissingPackagesActualNativeClonefileFailurePreservesErrnoAndTarget()
    {
        Skip.IfNot(OperatingSystem.IsMacOS(), "clonefile requires macOS");
        using var fixture = new MissingPackagesFixture();
        var cloner = new BeforePackagesNativeClone(
            () => Directory.Delete(fixture.DonorPackages, recursive: true));
        var runner = new RecordingWorktreeProcessRunner();

        var result = fixture.Ensure(runner, cloner);

        Assert.False(result.Success);
        fixture.AssertPreserved();
        Assert.False(Directory.Exists(fixture.Packages));
        Assert.Empty(Directory.EnumerateDirectories(fixture.Lake, "packages.stage-*"));
        AssertNoCacheGet(runner);
        using var receipt = ParseReceipt(result.Error);
        Assert.Equal(1, receipt.RootElement.GetProperty("clonefile_attempts").GetInt32());
        Assert.Equal(2, receipt.RootElement.GetProperty("clonefile_errno").GetInt32());
    }

    private sealed class BeforePackagesNativeClone(Action beforeClone) : IDirectoryCloner
    {
        public DirectoryCloneResult Clone(string source, string target)
        {
            beforeClone();
            return new ApfsDirectoryCloner().Clone(source, target);
        }
    }

    private sealed class MissingPackagesFixture : IDisposable
    {
        private readonly TemporaryDirectory repository = new();
        private readonly Dictionary<string, byte[]> preserved;
        private readonly string head;
        private readonly string index;
        private readonly byte[] indexBytes;

        internal MissingPackagesFixture(bool projectProbeFailure = false)
        {
            InitializeRepository(repository.Path);
            WriteCache(repository.Path, "warm main build\n", projectWarm: true);
            Target = AddWorktree(repository.Path, "missing-packages-target");
            WriteCache(Target, "unique target build\n", mathlibComplete: false, projectWarm: true);
            if (projectProbeFailure)
            {
                var project = Path.Combine(Lake, "build", "lib", "lean");
                Directory.Move(project, Path.Combine(Lake, "build", "preserved-project-oleans"));
                File.WriteAllText(project, "preserved non-directory project root\n");
            }
            WriteOwned("intake/unique.txt", "preserved intake\n");
            WriteOwned("build/reports/unique.json", "preserved partial report\n");
            File.WriteAllText(Path.Combine(Target, "README.md"), "preserved dirty source\n");
            File.WriteAllText(Path.Combine(Target, "proof-draft.txt"), "preserved untracked source\n");
            Git(Target, "add", "README.md");
            head = Git(Target, "rev-parse", "HEAD");
            index = Git(Target, "rev-parse", "--path-format=absolute", "--git-path", "index").Trim();
            indexBytes = File.ReadAllBytes(index);
            preserved = Directory.EnumerateFiles(Lake, "*", SearchOption.AllDirectories)
                .ToDictionary(static path => path, File.ReadAllBytes, StringComparer.Ordinal);
            var mergeHead = Git(Target, "rev-parse", "--path-format=absolute", "--git-path", "MERGE_HEAD").Trim();
            File.WriteAllText(mergeHead, head.Trim() + "\n");
            preserved.Add(mergeHead, File.ReadAllBytes(mergeHead));
        }

        internal string Repository => repository.Path;
        internal string Target { get; }
        internal string Lake => Path.Combine(Target, ".lake");
        internal string Packages => Path.Combine(Lake, "packages");
        internal string DonorLake => Path.Combine(LeanCacheGuard.PhysicalPath(Repository), ".lake");
        internal string DonorPackages => Path.Combine(DonorLake, "packages");

        internal CommandResult Ensure(IWorktreeProcessRunner runner, IDirectoryCloner cloner) =>
            WorktreeCommand.Run(Repository, ["ensure-cache", "--path", Target], runner, cloner);

        internal void AssertPreserved(bool exceptStamp = false)
        {
            foreach (var entry in preserved)
            {
                if (exceptStamp && entry.Key == LeanCacheStamp.PathFor(Lake)) continue;
                Assert.Equal(entry.Value, File.ReadAllBytes(entry.Key));
            }
            Assert.Equal(head, Git(Target, "rev-parse", "HEAD"));
            Assert.Equal(indexBytes, File.ReadAllBytes(index));
            Assert.Equal("preserved dirty source\n", File.ReadAllText(Path.Combine(Target, "README.md")));
            Assert.Equal("preserved untracked source\n", File.ReadAllText(Path.Combine(Target, "proof-draft.txt")));
        }

        internal void MakeDonorUnavailable(string failure)
        {
            switch (failure)
            {
                case "stamp-mismatch":
                    File.WriteAllText(Path.Combine(Repository, "lake-manifest.json"), LeanCacheFixtureFile.Manifest('b'));
                    StrataLint.TestSupport.RegPackageFixture.Write(Repository);
                    LeanCacheStamp.Write(DonorLake, ReadPins(Repository));
                    break;
                case "stamp-missing":
                    File.Delete(LeanCacheStamp.PathFor(DonorLake));
                    break;
                case "project-cold":
                    Directory.Delete(Path.Combine(DonorLake, "build", "lib", "lean"), recursive: true);
                    break;
                case "mathlib-cold":
                    Directory.Delete(Path.Combine(DonorPackages, "mathlib", ".lake", "build"), recursive: true);
                    break;
                case "packages-missing":
                    Directory.Delete(DonorPackages, recursive: true);
                    break;
                case "packages-symlink":
                    var backup = Path.Combine(Repository, "donor-packages-backup");
                    Directory.Move(DonorPackages, backup);
                    Directory.CreateSymbolicLink(DonorPackages, backup);
                    break;
                case "mathlib-symlink":
                    var mathlib = Path.Combine(DonorPackages, "mathlib");
                    var mathlibBackup = Path.Combine(Repository, "donor-mathlib-backup");
                    Directory.Move(mathlib, mathlibBackup);
                    Directory.CreateSymbolicLink(mathlib, mathlibBackup);
                    break;
                case "busy":
                    break;
                default:
                    throw new InvalidOperationException(failure);
            }
        }

        internal string CreatePackagesEntry(string kind)
        {
            if (kind == "file") File.WriteAllText(Packages, "owned packages file\n");
            else if (kind is "symlink" or "dangling-symlink")
            {
                var destination = Path.Combine(Target, "owned-packages");
                if (kind == "symlink") Directory.CreateDirectory(destination);
                Directory.CreateSymbolicLink(Packages, destination);
            }
            else
            {
                Directory.CreateDirectory(Packages);
                if (kind == "dirty") File.WriteAllText(Path.Combine(Packages, "dirty.txt"), "owned dirty dependency\n");
            }
            return PackagesEntryContents(kind);
        }

        internal string PackagesEntryContents(string kind) => kind switch
        {
            "file" => File.ReadAllText(Packages),
            "dirty" => File.ReadAllText(Path.Combine(Packages, "dirty.txt")),
            "symlink" or "dangling-symlink" => new DirectoryInfo(Packages).LinkTarget!,
            _ => string.Join('\n', Directory.EnumerateFileSystemEntries(Packages)),
        };

        private void WriteOwned(string relative, string contents)
        {
            var path = Path.Combine(Lake, relative);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, contents);
        }

        public void Dispose() => repository.Dispose();
    }
}
