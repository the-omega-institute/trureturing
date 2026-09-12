using System.Globalization;
using System.Reflection;
using System.Runtime.Loader;
using System.Text.Json;
using StrataLint.Cli;

namespace StrataLint.Tests;

[Collection(DefaultCliStartupCollection.Name)]
public sealed class DefaultCliStartupTests
{
    [Fact]
    public void DefaultCliValidatesBranchOutsideRepositoryWithoutScribeInputs()
    {
        using var temporary = new TemporaryDirectory();
        var branch = $"{WorktreeCommand.CreationNamespace}/{WorktreeCommand.CreationKinds[0]}/startup";

        var result = RunCli(temporary.Path, "worktree", "validate-branch", "--branch", branch);

        Assert.True(result.ExitCode == 0, result.StandardError);
        using var receipt = JsonDocument.Parse(result.StandardOutput);
        Assert.Equal("branch_validation", receipt.RootElement.GetProperty("event").GetString());
        Assert.Equal(branch, receipt.RootElement.GetProperty("branch").GetString());
        Assert.True(receipt.RootElement.GetProperty("canonical").GetBoolean());
    }

    [Fact]
    public void DefaultCliBulkCandidatesNeedNoLeanReportOrScribeDiscoveryFixtures()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        foreach (var (path, content) in fixture.Files)
        {
            var destination = Path.Combine(temporary.Path, path);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            TemporaryFileSystem.File.WriteAllText(destination, content);
        }
        ReviewRegressionTests.RunGit(temporary.Path, "init");
        ReviewRegressionTests.RunGit(temporary.Path, "add", ".");
        ReviewRegressionTests.RunGit(temporary.Path, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.test",
            "commit", "-m", "synthetic query baseline");

        var result = RunCli(temporary.Path, "digest-status", "--formalize-candidates");

        Assert.True(result.ExitCode == 0, result.StandardError);
        using var candidates = JsonDocument.Parse(result.StandardOutput);
        Assert.Equal("stratalint-formalize-candidates-v5", candidates.RootElement.GetProperty("schema").GetString());
    }

    private static (int ExitCode, string StandardOutput, string StandardError) RunCli(
        string root, params string[] arguments)
    {
        // Main must see the sparse fixture, and Scribe's static state must start fresh.
        var assemblyPath = typeof(Program).Assembly.Location;
        var context = new CliLoadContext(assemblyPath);
        using var output = new StringWriter(CultureInfo.InvariantCulture);
        using var error = new StringWriter(CultureInfo.InvariantCulture);
        var originalDirectory = Environment.CurrentDirectory;
        var originalOutput = Console.Out;
        var originalError = Console.Error;
        try
        {
            Environment.CurrentDirectory = root;
            Console.SetOut(output);
            Console.SetError(error);
            var assembly = context.LoadFromAssemblyPath(assemblyPath);
            var exitCode = (int)assembly.EntryPoint!.Invoke(null, [arguments])!;
            return (exitCode, output.ToString(), error.ToString());
        }
        finally
        {
            Console.SetError(originalError);
            Console.SetOut(originalOutput);
            Environment.CurrentDirectory = originalDirectory;
            context.Unload();
        }
    }

    private sealed class CliLoadContext(string assemblyPath) : AssemblyLoadContext(isCollectible: true)
    {
        private readonly AssemblyDependencyResolver resolver = new(assemblyPath);

        protected override Assembly? Load(AssemblyName assemblyName)
        {
            var path = resolver.ResolveAssemblyToPath(assemblyName);
            return path is null ? null : LoadFromAssemblyPath(path);
        }
    }
}

[CollectionDefinition(Name, DisableParallelization = true)]
public sealed class DefaultCliStartupCollection
{
    public const string Name = "Default CLI startup";
}
