using StrataLint.EngineeringScope;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.CiArtifacts.Tests;

public sealed class TransportIdentityTests
{
    [Theory]
    [InlineData("--stage", "unknown")]
    [InlineData("--commit", "short")]
    [InlineData("--commit", "zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz")]
    [InlineData("--run-id", "0")]
    [InlineData("--run-id", "-1")]
    [InlineData("--run-attempt", "0")]
    [InlineData("--run-attempt", "2147483648")]
    public void InvalidIdentityIsRejectedBeforeReadingOrWritingTheRepository(string field, string value)
    {
        using var directory = new TemporaryDirectory();
        var arguments = new[] { "transport-pack", "--repository", directory.Path,
            "--stage", "current", "--commit", new string('a', 40), "--run-id", "17",
            "--run-attempt", "2", "--archive", Path.Combine(directory.Path, "artifact.tgz") };
        arguments[Array.IndexOf(arguments, field) + 1] = value;
        var error = Assert.Throws<ArgumentException>(() => CiTransport.Run(arguments, TextWriter.Null));
        Assert.Equal("invalid transport stage or immutable execution identity", error.Message);
        Assert.Empty(Directory.EnumerateFileSystemEntries(directory.Path));
    }
}
