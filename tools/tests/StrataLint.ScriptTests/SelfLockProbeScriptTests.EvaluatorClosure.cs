using System.Text;

namespace StrataLint.Tests;

public sealed partial class SelfLockProbeScriptTests
{
    [Fact]
    public void AddingCompiledProbeSourceChangesEvaluatorDigest()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var controller = Path.Combine(temporary.Path, "controller");
        ScriptHarnessScratch.EnsureDirectory(controller);
        GitAt(controller, "init", "-b", "main");
        GitAt(controller, "config", "user.name", "Evaluator Closure Test");
        GitAt(controller, "config", "user.email", "evaluator-closure@example.invalid");
        foreach (var file in new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["Directory.Build.props"] = "<Project />\n",
            ["Directory.Packages.props"] = "<Project />\n",
            ["tools/scripts/workflow/pure-revert-detect.sh"] = "exit 0\n",
            ["tools/scripts/workflow/self-lock-probe.sh"] = "exit 0\n",
            ["tools/scripts/report/report-supervisor.sh"] = "exit 0\n",
            ["tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj"] =
                "<Project Sdk=\"Microsoft.NET.Sdk\" />\n",
            ["tools/StrataLint.EngineeringScope/Program.cs"] =
                "namespace Synthetic; internal static class Program;\n",
            ["tools/StrataLint.EngineeringScope/SelfLockProbe/StrictArtifacts.cs"] =
                "namespace Synthetic; internal static class StrictArtifacts;\n",
        })
        {
            var fullPath = Path.Combine(controller, file.Key);
            ScriptHarnessScratch.EnsureDirectory(Path.GetDirectoryName(fullPath)!);
            ScriptHarnessScratch.WriteScratchText(fullPath, file.Value);
        }
        GitAt(controller, "add", ".");
        GitAt(controller, "commit", "-m", "controller");

        var before = ReadEvaluatorDigest(controller);
        var added = Path.Combine(
            controller,
            "tools",
            "StrataLint.EngineeringScope",
            "SelfLockProbe",
            "AddedDecisionSource.cs");
        ScriptHarnessScratch.WriteScratchText(added, "namespace Added; internal sealed class Source;\n");
        GitAt(controller, "add", ".");
        GitAt(controller, "commit", "-m", "add compiled source");

        Assert.NotEqual(before, ReadEvaluatorDigest(controller));
    }

    private static string ReadEvaluatorDigest(string controller)
    {
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run(
            "dotnet",
            [
                Path.Combine(
                    root,
                    "tools",
                    "StrataLint.EngineeringScope",
                    "bin",
                    "Release",
                    "net10.0",
                    "StrataLint.EngineeringScope.dll"),
                "self-lock-probe",
                "evaluator-digest",
                "--controller-root",
                controller,
            ],
            root,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Empty(result.StandardError);
        return Encoding.UTF8.GetString(result.StandardOutput).Trim();
    }
}
