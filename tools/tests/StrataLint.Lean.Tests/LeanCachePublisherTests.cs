using StrataLint.EngineeringScope;
using StrataLint.TestSupport;

namespace StrataLint.Lean.Tests;

public sealed class LeanCachePublisherTests
{
    private static readonly LeanPinSet Pins = new(
        "toolchain"u8.ToArray(), "{}"u8.ToArray(), new string('a', 40));

    [Fact]
    public void PublishExcludesReleaseResidueBeforeRenameAndPreservesCachePayload()
    {
        using var scratch = new TemporaryDirectory();
        var staged = Path.Combine(scratch.Path, "staged");
        var target = Path.Combine(scratch.Path, "target");
        string[] residue = [".release-o_r76a09", ".release-backup-A9_z-7"];
        foreach (var name in residue)
            Write(staged, name + "/build/lib/lean/Failed.olean", "partial extraction");
        string[] retained =
        [
            "build/lib/lean/Project.olean",
            "packages/mathlib/.lake/build/lib/lean/Mathlib.olean",
            "build/.release-refreshed-at",
            "packages/mathlib/.release-nested/payload",
            ".release-/payload",
            ".release-a.b/payload",
            ".release-λ/payload",
            ".release-file123",
        ];
        foreach (var path in retained) Write(staged, path, path);
        var observed = false;
        var publisher = new LeanCachePublisher(published =>
        {
            observed = true;
            foreach (var name in residue) Assert.False(Directory.Exists(Path.Combine(published, name)));
            foreach (var path in retained) Assert.Equal(path, File.ReadAllText(Path.Combine(published, path)));
            Assert.False(File.Exists(LeanCacheStamp.PathFor(published)));
        });

        publisher.Publish(staged, target, Pins);

        Assert.True(observed);
        Assert.False(Directory.Exists(staged));
        Assert.True(LeanCacheStamp.Matches(target, Pins, out var reason), reason);
    }

    [Fact]
    public void PublishDeletesResidueSymlinksWithoutFollowingThemIntoTheDonor()
    {
        Skip.If(OperatingSystem.IsWindows(), "Creating symbolic links requires host privileges on Windows.");
        using var scratch = new TemporaryDirectory();
        var donor = Path.Combine(scratch.Path, "donor", ".lake");
        var staged = Path.Combine(scratch.Path, "staged");
        var target = Path.Combine(scratch.Path, "target");
        var donorBackup = Path.Combine(donor, ".release-backup-source123");
        Write(donorBackup, "build/retained", "donor backup");
        Write(donor, "build/retained", "donor build");
        var residue = Path.Combine(staged, ".release-extract123");
        Directory.CreateDirectory(residue);
        Directory.CreateSymbolicLink(Path.Combine(residue, "nested-link"), donorBackup);
        Directory.CreateSymbolicLink(Path.Combine(staged, ".release-backup-link123"), donorBackup);

        LeanCachePublisher.Instance.Publish(staged, target, Pins);

        Assert.False(Directory.Exists(Path.Combine(target, ".release-extract123")));
        Assert.False(Directory.Exists(Path.Combine(target, ".release-backup-link123")));
        Assert.Equal("donor backup", File.ReadAllText(Path.Combine(donorBackup, "build/retained")));
        Assert.Equal("donor build", File.ReadAllText(Path.Combine(donor, "build/retained")));
        Assert.True(LeanCacheStamp.Matches(target, Pins, out var reason), reason);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PublishFailureBeforeRenameLeavesAnExistingTargetUntouched(bool stageExists)
    {
        using var scratch = new TemporaryDirectory();
        var staged = Path.Combine(scratch.Path, "staged");
        var target = Path.Combine(scratch.Path, "target");
        Write(target, "sentinel", "existing target");
        if (stageExists) Write(staged, ".release-ab123/partial", "extraction");
        var observed = false;
        var publisher = new LeanCachePublisher(_ => observed = true);

        Assert.ThrowsAny<IOException>(() => publisher.Publish(staged, target, Pins));

        Assert.False(observed);
        Assert.Equal("existing target", File.ReadAllText(Path.Combine(target, "sentinel")));
        Assert.False(File.Exists(LeanCacheStamp.PathFor(target)));
        Assert.Equal(["sentinel"], Directory.GetFileSystemEntries(target).Select(Path.GetFileName));
    }

    private static void Write(string root, string relative, string content)
    {
        var path = Path.Combine(root, relative);
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllText(path, content);
    }
}
