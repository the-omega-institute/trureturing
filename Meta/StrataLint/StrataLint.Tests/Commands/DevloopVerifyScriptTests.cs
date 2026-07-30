using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

// The fkst devloop's local_iteration_result contract (v1) reads one full-line
// typed verdict marker from the local gate's output; an untyped nonzero exit
// is an honest UNKNOWN that dead-ends base-vs-candidate attribution and makes
// a single red terminal. devloop-verify.sh is this repository's single
// emission point of that marker around the local iteration gate.
public sealed class DevloopVerifyScriptTests
{
    [Theory]
    [InlineData("exit 0", 0, "PASS")]
    [InlineData("exit 1", 1, "SEMANTIC_FAIL")]
    [InlineData("exit 42", 42, "SEMANTIC_FAIL")]
    [InlineData("exit 126", 126, "UNKNOWN")]
    [InlineData("exit 127", 127, "UNKNOWN")]
    [InlineData("kill -TERM $$", 143, "UNKNOWN")]
    public void MarkerReflectsInnerOutcomeAndExitCodePassesThrough(
        string innerBody,
        int expectedExit,
        string expectedVerdict)
    {
        using var temporary = new TemporaryDirectory();
        var inner = Path.Combine(temporary.Path, "inner.sh");
        File.WriteAllText(inner, "#!/usr/bin/env bash\n" + innerBody + "\n");

        var result = BoundedProcessRunner.Run(
            "bash",
            [ScriptPath, "bash", inner],
            temporary.Path,
            TimeSpan.FromSeconds(30),
            1024 * 1024);

        Assert.Equal(expectedExit, result.ExitCode);
        var stdout = Encoding.UTF8.GetString(result.StandardOutput);
        var lines = stdout.Split('\n', StringSplitOptions.RemoveEmptyEntries);
        Assert.Equal($"FKST_LOCAL_ITERATION_RESULT:v1:{expectedVerdict}", lines[^1]);
    }

    // The marker line is the contract's whole grammar: exactly one declaration,
    // as the final stdout line, never duplicated (conflicting declarations are
    // themselves an UNKNOWN upstream).
    [Fact]
    public void ExactlyOneMarkerLineIsEmitted()
    {
        using var temporary = new TemporaryDirectory();
        var inner = Path.Combine(temporary.Path, "inner.sh");
        File.WriteAllText(inner, "#!/usr/bin/env bash\necho building\nexit 0\n");

        var result = BoundedProcessRunner.Run(
            "bash",
            [ScriptPath, "bash", inner],
            temporary.Path,
            TimeSpan.FromSeconds(30),
            1024 * 1024);

        var stdout = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.Equal(1, stdout.Split("FKST_LOCAL_ITERATION_RESULT:v1:").Length - 1);
    }

    private static string ScriptPath => Path.Combine(
        FindRepositoryRoot(),
        "Meta", "StrataLint", "scripts", "devloop-verify.sh");

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "Meta", "BACKFILL.yaml")))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}
