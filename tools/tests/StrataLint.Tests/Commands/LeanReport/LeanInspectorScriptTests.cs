using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LeanInspectorScriptTests
{
    [Theory]
    [InlineData("--output")]
    [InlineData("--repository")]
    [InlineData("--unknown")]
    public void InvalidInvocationNeverPublishes(string argument)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("bash", [Path.Combine(root, "tools/lean-inspector/inspect.sh"), argument], root,
            BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.Equal(2, result.ExitCode);
    }
}
