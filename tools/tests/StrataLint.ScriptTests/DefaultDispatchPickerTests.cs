using System.Text;

namespace StrataLint.Tests;

public sealed class DefaultDispatchPickerTests
{
    [Fact]
    public void FullFreshPrimeGenerationUsesProductionCliWithPrefixRelatedSources()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var fixture = Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures/default_dispatch_picker_contract.py");
        var result = TestProcessRunner.Run("python3", ["-B", fixture, root, "--production"], root,
            TimeSpan.FromSeconds(60), 2 * 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.Contains("PRODUCTION_DISPATCH_PICKERS_OK", Encoding.UTF8.GetString(result.StandardOutput), StringComparison.Ordinal);
    }

    [Fact]
    public void FreshAndCachedPickerEmissionUsesCurrentPolicyAndRestoration()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var fixture = Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures/default_dispatch_picker_contract.py");
        var result = TestProcessRunner.Run("python3", ["-B", fixture, root], root,
            TimeSpan.FromSeconds(60), 2 * 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.Contains("DEFAULT_DISPATCH_PICKERS_OK", Encoding.UTF8.GetString(result.StandardOutput), StringComparison.Ordinal);
    }
}
