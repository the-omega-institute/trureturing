using System.Text;
using StrataLint.TestSupport;

namespace StrataLint.WorkflowScript.Tests;

public sealed class ScriptHarnessScratchTests
{
    [Theory]
    [InlineData(false, 0)]
    [InlineData(false, 23)]
    [InlineData(true, 0)]
    [InlineData(true, 23)]
    public void ExecutableStubUsesItsShebangWithoutShellFallback(bool throughEnv, int childExit)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var stub = Path.Combine(temporary.Path, "executable with spaces");
        ScriptHarnessScratch.WriteExecutableStub(stub, """
            arguments=("$@")
            printf '%s\n' "${arguments[0]}"
            exit "${arguments[1]}"
            """);
        const string payload = "argument with spaces and Unicode: λ";
        // execv asks the kernel to honor the shebang, without a caller's shell
        // fallback hiding an invalid executable prefix. env covers the report
        // invocation boundary; even a successful fallback must not emit errors.
        string[] arguments = throughEnv
            ? [stub, payload, childExit.ToString(System.Globalization.CultureInfo.InvariantCulture)]
            : ["-B", "-c", "import os, sys; os.execv(sys.argv[1], sys.argv[1:])",
                stub, payload, childExit.ToString(System.Globalization.CultureInfo.InvariantCulture)];
        var result = TestProcessRunner.Run(throughEnv ? "env" : "python3", arguments,
            temporary.Path, TestBudgets.WorkflowProcessHangGuard, 8192);
        var error = Encoding.UTF8.GetString(result.StandardError);
        Assert.True(result.ExitCode == childExit, $"actual={result.ExitCode}\nstderr:\n{error}");
        Assert.Equal(payload + "\n", Encoding.UTF8.GetString(result.StandardOutput));
        Assert.True(error.Length == 0, error);
    }
}
