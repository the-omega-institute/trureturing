using StrataLint.Runtime;
using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

public sealed class WorktreeCopyPolicyTests
{
    [Fact]
    public void ExecutableSourcesUseTheCanonicalCopyImplementation()
    {
        var root = TestRepositoryLayout.FindRoot();
        var scan = Scan(root);
        Assert.True(scan.ExitCode == 1, System.Text.Encoding.UTF8.GetString(scan.StandardOutput));
    }

    [Theory]
    [InlineData("untracked")]
    [InlineData("staged")]
    [InlineData("unstaged")]
    [InlineData("committed")]
    public void CandidateSourceViolationsAreRejected(string state)
    {
        using var fixture = new TemporaryDirectory();
        Git(fixture.Path, "init", "--quiet");
        Git(fixture.Path, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
            "commit", "--quiet", "--allow-empty", "-m", "base");
        var source = Path.Combine(fixture.Path, "tools", "candidate.py");
        Directory.CreateDirectory(Path.GetDirectoryName(source)!);
        File.WriteAllText(source, "# canonical copy implementation\n");
        if (state is "unstaged")
        {
            Git(fixture.Path, "add", ".");
            Git(fixture.Path, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                "commit", "--quiet", "-m", "source");
        }
        Assert.Equal(1, Scan(fixture.Path).ExitCode);
        File.WriteAllText(source, string.Concat("# cp ", '-', "c source destination\n"));
        if (state is "staged" or "committed") Git(fixture.Path, "add", ".");
        if (state is "committed")
            Git(fixture.Path, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                "commit", "--quiet", "-m", "violation");
        var rejected = Scan(fixture.Path);
        Assert.Equal(0, rejected.ExitCode);
        Assert.Contains("tools/candidate.py:1:", System.Text.Encoding.UTF8.GetString(rejected.StandardOutput));
    }

    private static void Git(string root, params string[] arguments)
    {
        var result = TestProcessRunner.Run("git", arguments, root,
            BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.Equal(0, result.ExitCode);
    }

    private static ProcessOutput Scan(string root)
    {
        // Guard executable tooling; prose and truth data are not copy implementations.
        string[] inputs = ["**/*.lean", ".github/scripts/**", "Blueprint/**/*.scribe.cs",
            "Directory.Build.props", "Directory.Packages.props", "Makefile",
            "docs/reports/**/*.c", "docs/reports/**/*.cpp", "docs/reports/**/*.h",
            "docs/reports/**/*.mjs", "docs/reports/**/*.py", "tools/**"];
        // Build rejected forms dynamically so the guard does not match itself.
        var cloneFlag = string.Concat('-', 'c');
        var recursiveFlag = string.Concat('-', 'R');
        var shellForm = $"cp {cloneFlag}";
        var argumentForm = $"\"{cloneFlag}\", \"{recursiveFlag}\"";
        return TestProcessRunner.Run(
            "git",
            new[] { "grep", "--untracked", "-n", "-I", "-e", shellForm, "-e", argumentForm, "--" }
                .Concat(inputs.Select(input => ":(glob)" + input)).ToArray(),
            root,
            BoundedProcessRunner.HangDetectionBudget,
            1024 * 1024);

    }
}
