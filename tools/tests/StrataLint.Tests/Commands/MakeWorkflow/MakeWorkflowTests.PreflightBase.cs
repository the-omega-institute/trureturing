using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    [Fact]
    public void PreflightMakeTargetClearsOnlyTheFileDefault()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var root = TestRepositoryLayout.FindRoot();
        var scriptDirectory = Path.Combine(fixture.Path, "tools", "scripts");
        Directory.CreateDirectory(scriptDirectory);
        File.Copy(Path.Combine(root, "Makefile"), Path.Combine(fixture.Path, "Makefile"));
        WriteExecutable(
            Path.Combine(scriptDirectory, "preflight.sh"),
            "#!/usr/bin/env bash\nprintf '<%s>\\n' \"${BASE-__unset__}\"");

        var inherited = RunMakePreflight(fixture.Path, null, null);
        var environment = RunMakePreflight(fixture.Path, GateForkSha, null);
        var commandLine = RunMakePreflight(fixture.Path, null, GateCandidateSha);

        Assert.Equal("<>\n", Encoding.UTF8.GetString(inherited.StandardOutput));
        Assert.Equal($"<{GateForkSha}>\n", Encoding.UTF8.GetString(environment.StandardOutput));
        Assert.Equal($"<{GateCandidateSha}>\n", Encoding.UTF8.GetString(commandLine.StandardOutput));
    }

    private static ProcessOutput RunMakePreflight(
        string root,
        string? environmentBase,
        string? commandLineBase)
    {
        // MAKEFLAGS carries an ancestor make's command-line variables and a nested make
        // re-reads them as command-line origin, so clearing only BASE would let an outer
        // `make ... BASE=<sha>` decide this test's verdict. CI proved it: the engineering
        // job runs `make ... BASE=$ENGINEERING_BASE`, and this case observed that SHA
        // instead of the cleared file default. Judge the Makefile, not the ancestor.
        var arguments = new List<string> { "-u", "MAKEFLAGS", "-u", "MAKELEVEL" };
        if (environmentBase is null) arguments.AddRange(["-u", "BASE"]);
        else arguments.Add($"BASE={environmentBase}");
        arguments.Add("make");
        arguments.Add("--no-print-directory");
        arguments.Add("preflight");
        if (commandLineBase is not null) arguments.Add($"BASE={commandLineBase}");
        return TestProcessRunner.Run(
            "/usr/bin/env",
            arguments,
            root,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);
    }

}
