using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class LeanCacheEnsureCommandTests
{
    [Theory]
    [InlineData(false, null)]
    [InlineData(false, "1")]
    [InlineData(true, null)]
    public void MissingStampReaderRetiresFormerOwnersBeforeColdConsentOrWarmLaunch(
        bool currentWarm, string? consent)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "donor build");
        var donorFiles = WriteFormerOwners(repository.Path);
        var donorBefore = donorFiles.ToDictionary(path => path, File.ReadAllBytes);
        var target = AddWorktree(repository.Path, "writer-owner-transition");
        WriteCache(target, "target build", stamp: false, mathlibComplete: false);
        WriteSplitOwnership(target);
        var retired = WriteFormerOwners(target);
        var retained = currentWarm ? WriteCurrentOwners(target)
            : [OwnershipOutput(target, "stratalint/raw-lean-report.json")];
        var before = retained.ToDictionary(path => path,
            path => (Bytes: File.ReadAllBytes(path), Mtime: File.GetLastWriteTimeUtc(path)));
        var launches = 0;
        var runner = new RecordingWorktreeProcessRunner
        {
            DuringWrappedLake = root =>
            {
                Assert.Equal(LeanCacheGuard.PhysicalPath(target), LeanCacheGuard.PhysicalPath(root));
                Assert.All(retired, path => Assert.False(File.Exists(path), path));
                using var competingWriter = LeanCacheWriterGuard.TryAcquire(Path.Combine(target, ".lake"));
                Assert.Null(competingWriter);
                launches++;
            },
        };
        var cloner = new RecordingDirectoryCloner();
        var previous = Environment.GetEnvironmentVariable("STRATALINT_ACCEPT_COLD_BUILD");
        CommandResult result;
        try
        {
            Environment.SetEnvironmentVariable("STRATALINT_ACCEPT_COLD_BUILD", consent);
            result = WorktreeCommand.Run(repository.Path,
                ["with-cache-reader", "--path", target, "--", "lake", "build", "Reg.D5.Fixture"],
                runner, cloner);
        }
        finally
        {
            Environment.SetEnvironmentVariable("STRATALINT_ACCEPT_COLD_BUILD", previous);
        }

        var admitted = currentWarm || consent == "1";
        Assert.True(result.Success == admitted, result.Error);
        Assert.Equal(admitted ? 1 : 0, launches);
        Assert.Equal(admitted ? 1 : 0, runner.Invocations.Count(call =>
            call.FileName == "lake" && call.Arguments.SequenceEqual(["build", "Reg.D5.Fixture"])));
        if (!admitted) Assert.Contains("COLD_BUILD_REFUSED project olean cache is cold", result.Error);
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal(currentWarm ? "warm" : "cold", receipt.RootElement.GetProperty("project_olean_state").GetString());
        Assert.Equal("warm", receipt.RootElement.GetProperty("mathlib_olean_state").GetString());
        if (consent == "1") Assert.True(receipt.RootElement.GetProperty("cold_build_consent").GetBoolean());
        else Assert.False(receipt.RootElement.TryGetProperty("cold_build_consent", out _));
        Assert.Equal(2, cloner.Invocations.Count);
        Assert.All(retired, path => Assert.False(File.Exists(path), path));
        foreach (var path in retained)
        {
            Assert.Equal(before[path].Bytes, File.ReadAllBytes(path));
            Assert.Equal(before[path].Mtime, File.GetLastWriteTimeUtc(path));
        }
        foreach (var (path, bytes) in donorBefore) Assert.Equal(bytes, File.ReadAllBytes(path));
        Assert.Equal("target build", LeanCacheFixtureFile.ReadCacheText(target));
        Assert.True(LeanCacheStamp.Matches(Path.Combine(target, ".lake"), ReadPins(target), out _));
        using var released = LeanCacheWriterGuard.TryAcquire(Path.Combine(target, ".lake"));
        Assert.NotNull(released);
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void EnsureRetiresFormerRootOwnersAndRegButPreservesCurrentOwnersAndDependencyStamp(bool stamped)
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm", stamp: stamped);
        WriteSplitOwnership(repository.Path);
        var retired = WriteFormerOwners(repository.Path);
        var retained = WriteCurrentOwners(repository.Path);
        var stamp = LeanCacheStamp.PathFor(Path.Combine(repository.Path, ".lake"));
        var stampBytes = stamped ? File.ReadAllBytes(stamp) : null;
        var before = retained.ToDictionary(path => path,
            path => (Bytes: File.ReadAllBytes(path), Mtime: File.GetLastWriteTimeUtc(path)));

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], new RecordingWorktreeProcessRunner());

        Assert.True(result.Success, result.Error);
        Assert.All(retired, path => Assert.False(File.Exists(path), path));
        foreach (var path in retained)
        {
            Assert.Equal(before[path].Bytes, File.ReadAllBytes(path));
            Assert.Equal(before[path].Mtime, File.GetLastWriteTimeUtc(path));
        }
        if (stamped) Assert.Equal(stampBytes, File.ReadAllBytes(stamp));
        var reg = OwnershipOutput(repository.Path, "reg/lib/lean/Reg/Recovered.olean");
        var recoveredTime = File.GetLastWriteTimeUtc(reg);
        var repeated = WorktreeCommand.Run(repository.Path, ["ensure-cache"], new RecordingWorktreeProcessRunner());
        Assert.True(repeated.Success, repeated.Error);
        Assert.Equal("owned output", File.ReadAllText(reg));
        Assert.Equal(recoveredTime, File.GetLastWriteTimeUtc(reg));
    }

    [Fact]
    public void DonorRetirementRunsAfterCloneAndLeavesDonorUnchanged()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor");
        var donorFiles = WriteFormerOwners(repository.Path);
        var target = AddWorktree(repository.Path, "owner-transition");
        WriteSplitOwnership(target);

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner(), new RecordingDirectoryCloner());

        Assert.True(result.Success, result.Error);
        Assert.All(donorFiles, path => Assert.Equal("owned output", File.ReadAllText(path)));
        Assert.All(donorFiles, path => Assert.False(File.Exists(Path.Combine(target, Path.GetRelativePath(repository.Path, path)))));
        Assert.True(LeanCacheStamp.Matches(Path.Combine(target, ".lake"), ReadPins(target), out _));
    }

    [Fact]
    public void RootLibrariesThatStillOwnJudgeSourcesArePreserved()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm");
        WriteSplitOwnership(repository.Path);
        File.AppendAllText(Path.Combine(repository.Path, "lakefile.toml"),
            "[[lean_lib]]\nname = \"LeanInformationAudit\"\n[[lean_lib]]\nname = \"LeanInformationAuditAnalysis\"\n");
        var retained = WriteFormerOwners(repository.Path);

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], new RecordingWorktreeProcessRunner());

        Assert.True(result.Success, result.Error);
        Assert.All(retained, path => Assert.True(File.Exists(path), path));
    }

    [Fact]
    public void FormerJudgeOleansDoNotCountAsProjectWarmthAfterRetirement()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm", mathlibComplete: false);
        WriteSplitOwnership(repository.Path);
        WriteFormerOwners(repository.Path);

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], new RecordingWorktreeProcessRunner());

        Assert.True(result.Success, result.Error);
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("cold", receipt.RootElement.GetProperty("project_olean_state").GetString());
        Assert.Equal("cold", receipt.RootElement.GetProperty("mathlib_olean_state").GetString());
    }

    [Theory]
    [InlineData("lib")]
    [InlineData("lib/lean/LeanInformationAudit")]
    [InlineData("lib/lean/LeanInformationAudit/linked")]
    [InlineData("reg")]
    [InlineData("reg/linked")]
    public void OwnershipRetirementRejectsSymlinksBeforeDeletingAnyOutput(string relative)
    {
        if (OperatingSystem.IsWindows()) return;
        using var repository = new TemporaryDirectory();
        using var outside = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm");
        WriteSplitOwnership(repository.Path);
        var obsolete = OwnershipOutput(repository.Path, "ir/LeanInformationAudit/Keep.c");
        var protectedFile = Path.Combine(outside.Path, "keep");
        File.WriteAllText(protectedFile, "outside");
        var link = Path.Combine(repository.Path, ".lake/build", relative);
        Directory.CreateDirectory(Path.GetDirectoryName(link)!);
        Directory.CreateSymbolicLink(link, outside.Path);

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], new RecordingWorktreeProcessRunner());

        Assert.False(result.Success);
        Assert.True(File.Exists(obsolete));
        Assert.Equal("outside", File.ReadAllText(protectedFile));
    }

    [Fact]
    public void OwnershipRetirementRejectsNonDirectoryOutputAndWrongOrDisposedGuard()
    {
        using var repository = new TemporaryDirectory();
        using var other = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm");
        WriteSplitOwnership(repository.Path);
        var retired = WriteFormerOwners(repository.Path);
        using var wrong = LeanCacheWriterGuard.TryAcquire(Path.Combine(other.Path, ".lake"));
        Assert.NotNull(wrong);
        Assert.Throws<InvalidOperationException>(() => LeanCacheEnsureCommand.RetireRootJudgeOutputs(repository.Path, wrong));
        using var correct = LeanCacheWriterGuard.TryAcquire(Path.Combine(repository.Path, ".lake"));
        Assert.NotNull(correct);
        correct.Dispose();
        Assert.Throws<ObjectDisposedException>(() => LeanCacheEnsureCommand.RetireRootJudgeOutputs(repository.Path, correct));
        Assert.All(retired, path => Assert.True(File.Exists(path)));
        var invalid = OwnershipOutput(repository.Path, "ir/LeanInformationAuditAnalysis");
        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], new RecordingWorktreeProcessRunner());
        Assert.False(result.Success);
        Assert.Contains("not a private directory", result.Error);
        Assert.True(File.Exists(invalid));
        Assert.All(retired, path => Assert.True(File.Exists(path)));
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    [InlineData(3)]
    public void InterruptedRetirementRetriesWithoutLeavingContaminatedReg(int completedRemovals)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm");
        WriteSplitOwnership(repository.Path);
        var retired = WriteFormerOwners(repository.Path);
        using (var guard = LeanCacheWriterGuard.TryAcquire(Path.Combine(repository.Path, ".lake")))
        {
            Assert.NotNull(guard);
            var calls = 0;
            Assert.Throws<IOException>(() => LeanCacheEnsureCommand.RetireRootJudgeOutputs(repository.Path, guard, path =>
            {
                if (calls++ == completedRemovals) throw new IOException("interrupted retirement");
                Directory.Delete(path, recursive: true);
            }));
        }
        Assert.True(Directory.Exists(Path.Combine(repository.Path, ".lake/build/lib/lean/LeanInformationAuditAnalysis")));
        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], new RecordingWorktreeProcessRunner());
        Assert.True(result.Success, result.Error);
        Assert.All(retired, path => Assert.False(File.Exists(path)));
    }

    private static void WriteSplitOwnership(string root) => File.WriteAllText(Path.Combine(root, "lakefile.toml"),
        "name = \"trureturing\"\n[[lean_lib]]\nname = \"Trureturing\"\nroots = [\"Trureturing\", \"D5\"]\n");

    private static string[] WriteFormerOwners(string root) =>
    [
        OwnershipOutput(root, "lib/lean/LeanInformationAudit/Registry/Assessment.olean"),
        OwnershipOutput(root, "ir/LeanInformationAudit/Registry/Assessment.c.o"),
        OwnershipOutput(root, "lib/lean/LeanInformationAuditAnalysis/SealBaseline.olean"),
        OwnershipOutput(root, "reg/lib/lean/Reg/Contaminated.olean"),
        OwnershipOutput(root, "reg/ir/LeanInformationAuditRegTests/Native.c"),
    ];

    private static string[] WriteCurrentOwners(string root) =>
    [
        OwnershipOutput(root, "lib/lean/D5/Keep.olean"),
        OwnershipOutput(root, "ir/D5/Keep.c.o"),
        OwnershipOutput(root, "lib/lean/Trureturing.olean"),
        OwnershipOutput(root, "lean-inspector/producer/lib/lean/LeanInformationAudit/Registry/Assessment.olean"),
        OwnershipOutput(root, "lean-inspector/interface/lib/lean/LeanInformationAuditInterface/Keep.olean"),
        OwnershipOutput(root, "lean-inspector/modules/Keep.zip"),
        OwnershipOutput(root, "stratalint/raw-lean-report.json"),
        OwnershipOutput(root, "../packages/mathlib/.lake/build/lib/lean/Mathlib/Keep.olean"),
    ];

    private static string OwnershipOutput(string root, string relative)
    {
        var path = Path.GetFullPath(Path.Combine(root, ".lake/build", relative));
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllText(path, "owned output");
        return path;
    }
}
