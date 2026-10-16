using System.Text;

namespace StrataLint.Tests;

public sealed class ScriptHarnessScratchTests
{
    [Theory]
    [InlineData("direct", 0)]
    [InlineData("direct", 23)]
    [InlineData("shell", 0)]
    [InlineData("shell", 23)]
    [InlineData("env", 0)]
    [InlineData("env", 23)]
    public void ExecutableStubPreservesBashArgumentsEnvironmentAndExit(string invocation, int exitCode)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var stub = Path.Combine(temporary.Path, "executable stub");
        ScriptHarnessScratch.WriteExecutableStub(stub, """
            values=("$1" "$SCRATCH_TEST_VALUE")
            printf '%s|%s\n' "${values[0]}" "${values[1]}"
            printf 'stub diagnostic λ\n' >&2
            exit "$2"
            """);
        var arguments = new List<string> { "SCRATCH_TEST_VALUE=value λ" };
        if (invocation == "direct")
            arguments.AddRange(["python3", "-B", "-c",
                "import os, sys; os.execv(sys.argv[1], sys.argv[1:])"]);
        else if (invocation == "shell")
            arguments.AddRange(["/bin/bash", "-c", "\"$@\"", "stub-shell"]);
        arguments.AddRange([stub, "argument with spaces λ", exitCode.ToString(System.Globalization.CultureInfo.InvariantCulture)]);
        var result = TestProcessRunner.Run("env", arguments, temporary.Path,
            TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        var output = Encoding.UTF8.GetString(result.StandardOutput);
        var error = Encoding.UTF8.GetString(result.StandardError);

        var diagnostics = $"[FAIL] executable_stub_{invocation}: expected={exitCode} actual={result.ExitCode}"
            + $"\nexecutable_prefix={Convert.ToHexString(ScriptHarnessScratch.ReadScratchBytes(stub).AsSpan(0, 8))}"
            + $"\nstdout:\n{output}\nstderr:\n{error}";
        Assert.True(result.ExitCode == exitCode, diagnostics);
        Assert.True(output == "argument with spaces λ|value λ\n", diagnostics);
        Assert.True(error == "stub diagnostic λ\n", diagnostics);
    }
}
