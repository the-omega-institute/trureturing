using StrataLint.TestSupport;
using Xunit;
using FactAttribute = Xunit.SkippableFactAttribute;
using TheoryAttribute = Xunit.SkippableTheoryAttribute;

namespace StrataLint.Cache.Tests;

public sealed class ScriptProcessOutputTests
{
    [Theory]
    [InlineData("stdout", "123456789")]
    [InlineData("stderr", "123456789")]
    [InlineData("stdout", "界界界")]
    [InlineData("stderr", "界界界")]
    public void SuccessfulExitCannotAcceptOutputAboveTheByteLimit(string stream, string value)
    {
        using var directory = new TemporaryDirectory();
        var failure = Assert.Throws<InvalidOperationException>(() => EngineeringProcess.Capture(
            directory.Path, "python3", ["-c", $"import sys; sys.{stream}.write(sys.argv[1])", value],
            maximumOutputBytes: 8));
        Assert.Contains("process output exceeded 8 bytes", failure.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("12345678", 8)]
    [InlineData("界界", 6)]
    public void EachOutputStreamAcceptsItsOwnExactByteLimit(string value, int limit)
    {
        using var directory = new TemporaryDirectory();
        var result = EngineeringProcess.Capture(directory.Path, "python3",
            ["-c", "import sys; sys.stdout.write(sys.argv[1]); sys.stderr.write(sys.argv[1])", value],
            maximumOutputBytes: limit);
        Assert.Equal(0, result.Exit);
        Assert.Equal(value, result.StandardOutput);
        Assert.Equal(value, result.StandardError);
    }

    [Fact]
    public void CombinedOutputKeepsBothStreamsAndTheChildExit()
    {
        using var directory = new TemporaryDirectory();
        var result = EngineeringProcess.Process(directory.Path, "python3",
            ["-c", "import sys; sys.stdout.write('out'); sys.stderr.write('err'); sys.exit(7)"],
            maximumOutputBytes: 3);
        Assert.Equal(7, result.Exit);
        Assert.Equal("outerr", result.Text);
    }
}
