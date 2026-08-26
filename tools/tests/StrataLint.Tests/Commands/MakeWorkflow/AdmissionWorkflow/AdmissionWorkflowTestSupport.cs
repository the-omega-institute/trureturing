using StrataLint.Engine;
using YamlDotNet.RepresentationModel;

namespace StrataLint.Tests;

public sealed partial class AdmissionWorkflowTests
{
    private static void WriteFloorProject(string repository, string assembly, string className)
    {
        var directory = Path.Combine(repository, "tools", "tests", assembly);
        Directory.CreateDirectory(directory);
        File.WriteAllText(
            Path.Combine(directory, $"{assembly}.csproj"),
            $"""
            <Project Sdk="Microsoft.NET.Sdk">
              <PropertyGroup><TargetFramework>net10.0</TargetFramework><IsTestProject>true</IsTestProject><AssemblyName>{assembly}</AssemblyName><RestorePackagesWithLockFile>false</RestorePackagesWithLockFile></PropertyGroup>
              <ItemGroup><PackageReference Include="Microsoft.NET.Test.Sdk" Version="18.0.1" /><PackageReference Include="xunit" Version="2.9.3" /><PackageReference Include="xunit.runner.visualstudio" Version="3.1.4" /></ItemGroup>
            </Project>
            """);
        File.WriteAllText(
            Path.Combine(directory, "FloorProbe.cs"),
            $"using System; using System.IO; using Xunit; public sealed class {className} {{ [Fact] public void Runs() => File.AppendAllText(Environment.GetEnvironmentVariable(\"ENGINEERING_FLOOR_MARKER\")!, \"{assembly}\\n\"); }}\n");
    }

    private static string StepScript(IEnumerable<YamlMappingNode> steps, string name)
    {
        var step = Assert.Single(steps, candidate => StepName(candidate) == name);
        return Assert.IsType<YamlScalarNode>(step.Children[new YamlScalarNode("run")]).Value
            ?? string.Empty;
    }

    private static ProcessOutput RunEngineeringScope(
        string engineeringRoot,
        string repositoryRoot,
        string planFile,
        string head,
        string @base,
        params string[] environment) =>
        RunEngineeringScopeMode(engineeringRoot, repositoryRoot, planFile, head, @base, "execute", environment);

    private static ProcessOutput RunEngineeringScopeMode(
        string engineeringRoot,
        string repositoryRoot,
        string planFile,
        string head,
        string @base,
        string mode,
        params string[] environment)
    {
        var project = Path.Combine(
            engineeringRoot,
            "tools",
            "StrataLint.EngineeringScope",
            "StrataLint.EngineeringScope.csproj");
        var build = BoundedProcessRunner.Run(
            DotnetHost(engineeringRoot),
            ["build", project, "--configuration", "Release", "--no-restore", "--nologo"],
            engineeringRoot,
            TimeSpan.FromMinutes(2),
            2 * 1024 * 1024);
        Assert.True(
            build.ExitCode == 0,
            System.Text.Encoding.UTF8.GetString(build.StandardOutput)
                + System.Text.Encoding.UTF8.GetString(build.StandardError));
        var arguments = new List<string>(environment)
        {
            DotnetHost(engineeringRoot),
            "run",
            "--project",
            project,
            "--configuration",
            "Release",
            "--no-launch-profile",
            "--no-build",
            "--no-restore",
            "--",
            "--mode",
            mode,
            "--repository",
            repositoryRoot,
            "--head",
            head,
            "--base",
            @base,
            "--plan-file",
            planFile,
        };
        return BoundedProcessRunner.Run(
            "env",
            arguments,
            repositoryRoot,
            TimeSpan.FromMinutes(2),
            2 * 1024 * 1024);
    }

    private static string DotnetHost(string root)
    {
        var result = BoundedProcessRunner.Run(
            "/bin/sh",
            ["-c", "command -v dotnet"],
            root,
            TimeSpan.FromSeconds(10),
            4096);
        Assert.Equal(0, result.ExitCode);
        return System.Text.Encoding.UTF8.GetString(result.StandardOutput).Trim();
    }

    private static string GitText(string repository, params string[] arguments)
    {
        var result = BoundedProcessRunner.Run(
            "git",
            ["-C", repository, .. arguments],
            repository,
            TimeSpan.FromSeconds(30),
            64 * 1024);
        Assert.Equal(0, result.ExitCode);
        return System.Text.Encoding.UTF8.GetString(result.StandardOutput).Trim();
    }

    private static void Git(string repository, params string[] arguments) =>
        _ = GitText(repository, arguments);

    private static void WriteExecutable(string path, string content)
    {
        File.WriteAllText(path, content);
        if (OperatingSystem.IsWindows()) return;
        File.SetUnixFileMode(
            path,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
    }

    private static string ReadTemporaryText(string path)
    {
        using var reader = new StreamReader(path);
        return reader.ReadToEnd();
    }

    private static string JobText(string workflow, string job, string nextJob)
    {
        var start = workflow.IndexOf($"  {job}:\n", StringComparison.Ordinal);
        var end = workflow.IndexOf($"  {nextJob}:\n", start, StringComparison.Ordinal);
        Assert.True(start >= 0 && end > start);
        return workflow[start..end];
    }

    private static string AdmissionWorkflow() =>
        File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), ".github", "workflows", "ci.yml"));

    private static YamlMappingNode Jobs(string workflow)
    {
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var document = Assert.IsType<YamlMappingNode>(stream.Documents[0].RootNode);
        return Assert.IsType<YamlMappingNode>(document.Children[new YamlScalarNode("jobs")]);
    }

    private static YamlMappingNode Job(string workflow, string job) =>
        Assert.IsType<YamlMappingNode>(Jobs(workflow).Children[new YamlScalarNode(job)]);

    private static YamlMappingNode[] JobSteps(string workflow, string job) =>
        Assert.IsType<YamlSequenceNode>(Job(workflow, job).Children[new YamlScalarNode("steps")])
            .Children
            .OfType<YamlMappingNode>()
            .ToArray();

    private static string StepName(YamlMappingNode step) =>
        Assert.IsType<YamlScalarNode>(step.Children[new YamlScalarNode("name")]).Value ?? string.Empty;

    private static bool BaselineNeedsExactlyLeanInspect(string workflow) =>
        Needs(Job(workflow, "baseline-admission")).SequenceEqual(["lean-inspect"], StringComparer.Ordinal);

    private static IEnumerable<string> Needs(YamlMappingNode job)
    {
        if (!job.Children.TryGetValue(new YamlScalarNode("needs"), out var needs)) yield break;
        if (needs is YamlScalarNode scalar)
        {
            yield return scalar.Value!;
            yield break;
        }
        foreach (var item in Assert.IsType<YamlSequenceNode>(needs).Children.OfType<YamlScalarNode>())
            yield return item.Value!;
    }

    private static string BaselineResolutionScript(string workflow)
    {
        var leanInspect = Assert.IsType<YamlMappingNode>(
            Jobs(workflow).Children[new YamlScalarNode("lean-inspect")]);
        var steps = Assert.IsType<YamlSequenceNode>(
            leanInspect.Children[new YamlScalarNode("steps")]);
        var step = Assert.Single(
            steps.Children.OfType<YamlMappingNode>(),
            node => node.Children.TryGetValue(new YamlScalarNode("id"), out var id)
                && id is YamlScalarNode { Value: "base" });
        return Assert.IsType<YamlScalarNode>(step.Children[new YamlScalarNode("run")]).Value ?? string.Empty;
    }
}
