using System.Runtime.InteropServices;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class DirectoryClonerTests
{
    [Fact]
    public void NonMacOsReturnsWithoutCallingClonefile()
    {
        var nativeCalls = 0;
        var cloner = new ApfsDirectoryCloner(
            isMacOS: static () => false,
            cloneFile: (_, _, _) =>
            {
                nativeCalls++;
                return 0;
            });

        var result = cloner.Clone("source", "target");

        Assert.False(result.Succeeded);
        Assert.Null(result.Errno);
        Assert.Equal(0, nativeCalls);
    }

    [Theory]
    [InlineData(5)]   // EIO
    [InlineData(4)]   // EINTR
    [InlineData(35)]  // EAGAIN
    [InlineData(16)]  // EBUSY
    [InlineData(999)]
    public void NativeFailurePreservesErrno(int errno)
    {
        var nativeCalls = 0;
        var cloner = new ApfsDirectoryCloner(
            isMacOS: static () => true,
            cloneFile: (_, _, _) =>
            {
                nativeCalls++;
                Marshal.SetLastPInvokeError(errno);
                return -1;
            });

        var result = cloner.Clone("source", "target");

        Assert.False(result.Succeeded);
        Assert.Equal(errno, result.Errno);
        Assert.Equal(1, nativeCalls);
    }
}
