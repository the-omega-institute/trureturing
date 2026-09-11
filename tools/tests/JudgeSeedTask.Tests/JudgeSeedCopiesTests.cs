using Microsoft.Build.Utilities;
using StrataLint.JudgeSeed;
using StrataLint.TestSupport;
using Xunit;

namespace JudgeSeedTask.Tests;

public sealed class JudgeSeedCopiesTests : IDisposable
{
    private readonly string root = TemporaryFileSystem.Directory.CreateTempSubdirectory("judge-seed-copies-").FullName;
    private static readonly DateTime Stamp = new(2000, 1, 1, 0, 0, 0, DateTimeKind.Utc);

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ChangedBytesWithEqualLengthAndTimestampAreRepairedBeforeNativeCopy(bool folder)
    {
        var source = Write("source/payload", [0, 255, 1, 2]);
        var destination = Write("destination/payload", [0, 254, 1, 2]);
        var task = Copies(source, destination, folder);

        Assert.True(task.Execute());
        Assert.True(TemporaryFileSystem.File.Exists(destination));
        Assert.Equal(new byte[] { 0, 255, 1, 2 }, TemporaryFileSystem.File.ReadAllBytes(source));

        Copy(source, destination);
        Assert.Equal(new byte[] { 0, 255, 1, 2 }, TemporaryFileSystem.File.ReadAllBytes(destination));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EqualBytesAndModesKeepTheDestination(bool folder)
    {
        var source = Write("source/payload", [0, 255, 1, 2]);
        var destination = Write("destination/payload", [0, 255, 1, 2]);

        Assert.True(Copies(source, destination, folder).Execute());

        Assert.Equal(new byte[] { 0, 255, 1, 2 }, TemporaryFileSystem.File.ReadAllBytes(destination));
        Assert.Equal(Stamp, File.GetLastWriteTimeUtc(destination));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ModeOnlyDifferenceInvalidatesTheDestination(bool folder)
    {
        if (OperatingSystem.IsWindows()) return;
        var source = Write("source/payload", [0, 255, 1, 2]);
        var destination = Write("destination/payload", [0, 255, 1, 2]);
        var executable = UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute;
        File.SetUnixFileMode(source, executable);
        File.SetUnixFileMode(destination, UnixFileMode.UserRead | UnixFileMode.UserWrite);

        Assert.True(Copies(source, destination, folder).Execute());
        Assert.True(TemporaryFileSystem.File.Exists(destination));
        Assert.Equal(executable, File.GetUnixFileMode(source));

        Copy(source, destination);
        Assert.Equal(executable, File.GetUnixFileMode(destination));
        Assert.Equal(new byte[] { 0, 255, 1, 2 }, TemporaryFileSystem.File.ReadAllBytes(destination));
    }

    [Fact]
    public void ExplicitDestinationsPairByIndexAndLeaveEqualFilesAlone()
    {
        var first = Write("a", [1]);
        var second = Write("b", [2]);
        var keep = Write("renamed-second", [2]);
        var remove = Write("renamed-first", [9]);
        var task = new JudgeSeedCopies
        {
            SourceFiles = [new TaskItem(first), new TaskItem(second)],
            DestinationFiles = [new TaskItem(remove), new TaskItem(keep)],
        };

        Assert.True(task.Execute());
        Assert.Equal(new byte[] { 1 }, TemporaryFileSystem.File.ReadAllBytes(remove));
        Assert.Equal(new byte[] { 2 }, TemporaryFileSystem.File.ReadAllBytes(keep));
    }

    [Fact]
    public void SamePathMissingDestinationAndEmptySourcesAreNoOps()
    {
        var source = Write("payload", [1, 2]);
        Assert.True(Copies(source, Path.Combine(root, ".", "payload"), false).Execute());
        Assert.Equal(new byte[] { 1, 2 }, TemporaryFileSystem.File.ReadAllBytes(source));
        var missing = Path.Combine(root, "missing");
        Assert.True(Copies(source, missing, false).Execute());
        Assert.False(TemporaryFileSystem.File.Exists(missing));
        Assert.True(new JudgeSeedCopies().Execute());
    }

    [Fact]
    public void MissingSourceDoesNotDeleteAnExistingDestination()
    {
        var destination = Write("payload", [7]);

        Assert.Throws<FileNotFoundException>(() => Copies(Path.Combine(root, "missing"), destination, false).Execute());

        Assert.Equal(new byte[] { 7 }, TemporaryFileSystem.File.ReadAllBytes(destination));
    }

    [Fact]
    public void StagingFailureLeavesTheExistingDestinationIntact()
    {
        if (OperatingSystem.IsWindows()) return;
        var source = Write("source/payload", [1]);
        var destination = Write("readonly/payload", [9]);
        var directory = Path.GetDirectoryName(destination)!;
        var mode = File.GetUnixFileMode(directory);
        try
        {
            File.SetUnixFileMode(directory, UnixFileMode.UserRead | UnixFileMode.UserExecute);
            Assert.Throws<UnauthorizedAccessException>(() => Copies(source, destination, false).Execute());
            Assert.Equal(new byte[] { 9 }, TemporaryFileSystem.File.ReadAllBytes(destination));
        }
        finally { File.SetUnixFileMode(directory, mode); }
    }

    private string Write(string relative, byte[] bytes)
    {
        var path = Path.Combine(root, relative);
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        TemporaryFileSystem.File.WriteAllBytes(path, bytes);
        File.SetLastWriteTimeUtc(path, Stamp);
        return path;
    }

    private static JudgeSeedCopies Copies(string source, string destination, bool folder) => new()
    {
        SourceFiles = [new TaskItem(source)],
        DestinationFiles = folder ? null : [new TaskItem(destination)],
        DestinationFolder = folder ? Path.GetDirectoryName(destination) : null,
    };

    private static void Copy(string source, string destination) => Assert.True(new Microsoft.Build.Tasks.Copy
    {
        BuildEngine = new CaptureBuildEngine(),
        SourceFiles = [new TaskItem(source)],
        DestinationFiles = [new TaskItem(destination)],
        SkipUnchangedFiles = true,
    }.Execute());

    public void Dispose() => TemporaryFileSystem.Directory.Delete(root, recursive: true);
}
