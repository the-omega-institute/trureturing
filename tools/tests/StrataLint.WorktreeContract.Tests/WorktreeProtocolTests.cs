using System.Text;
using StrataLint.Runtime;
using Xunit;
using Xunit.Abstractions;

namespace StrataLint.WorktreeContract.Tests;

public sealed class WorktreeProtocolTests(ITestOutputHelper output)
{
    [Fact]
    public void DisposableGitLifecycleHonorsAgeAndNativeStalePolicy()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var script = Path.Combine(root,
            "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/stale_lifecycle_cases.py");
        var result = TestProcessRunner.Run("python3", ["-B", script, root], root,
            TimeSpan.FromSeconds(180), 1024 * 1024);
        output.WriteLine(Encoding.UTF8.GetString(result.StandardOutput));
        output.WriteLine(Encoding.UTF8.GetString(result.StandardError));
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
