using System.Diagnostics;
using System.Text.Json;
using StrataLint.EngineeringScope;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class EngineeringScopeProgramTests
{
    private const string ProductProject = "tools/Product/Product.csproj";
    private const string ProductTestsProject =
        "tools/tests/Product.Tests/Product.Tests.csproj";
    private const string NewProductProject = "tools/NewProduct/NewProduct.csproj";
    private const string NewProductTestsProject =
        "tools/tests/NewProduct.Tests/NewProduct.Tests.csproj";

    [Fact]
    public void CandidateNewTestProjectIsSelectedOnItsIntroducingChange()
    {
        var result = RunBoundary(
            root =>
            {
                WriteProject(root, ProductProject, isTest: false);
                WriteProject(root, ProductTestsProject, isTest: true, ProductProject);
            },
            root =>
            {
                WriteProject(root, NewProductProject, isTest: false);
                WriteProject(root, NewProductTestsProject, isTest: true, NewProductProject);
            });

        Assert.True(result.ExitCode == 0, result.Diagnostic);
        Assert.Equal(
            [NewProductTestsProject, ProductTestsProject],
            result.SelectedProjects);
    }

    [Fact]
    public void CandidateNewXunitProjectWithoutLiteralIsTestProjectIsSelected()
    {
        var result = RunBoundary(
            root =>
            {
                WriteProject(root, ProductProject, isTest: false);
                WriteProject(root, ProductTestsProject, isTest: true, ProductProject);
            },
            root => WriteRunnableTestProjectWithoutMarker(
                root,
                NewProductTestsProject,
                ProductProject));

        Assert.True(result.ExitCode == 0, result.Diagnostic);
        Assert.Equal(
            [NewProductTestsProject, ProductTestsProject],
            result.SelectedProjects);
    }

    [Fact]
    public void CandidateNewProjectWithNonLiteralTestClassificationFailsClosed()
    {
        var result = RunBoundary(
            root =>
            {
                WriteProject(root, ProductProject, isTest: false);
                WriteProject(root, ProductTestsProject, isTest: true, ProductProject);
            },
            root => WriteFile(
                root,
                "tools/tests/Ambiguous.Tests/Ambiguous.Tests.csproj",
                """
                <Project Sdk="Microsoft.NET.Sdk">
                  <PropertyGroup><IsTestProject>$(CandidateIsTest)</IsTestProject></PropertyGroup>
                </Project>
                """));

        Assert.True(result.ExitCode == 2, result.Diagnostic);
        Assert.Contains(
            "candidate-added project has no literal IsTestProject classification",
            result.Error,
            StringComparison.Ordinal);
    }

    [Fact]
    public void CandidateProjectReferenceDeletionCannotShrinkBaseSelection()
    {
        const string scribeProject =
            "tools/StrataLint.Scribe/StrataLint.Scribe.csproj";
        const string scribeTestsProject =
            "tools/tests/StrataLint.Scribe.Tests/StrataLint.Scribe.Tests.csproj";
        var result = RunBoundary(
            root =>
            {
                WriteProject(root, scribeProject, isTest: false);
                WriteProject(root, scribeTestsProject, isTest: true, scribeProject);
                WriteFile(root, "tools/StrataLint.Scribe/DocumentEmitter.cs", "// base\n");
            },
            root =>
            {
                WriteRunnableTestProjectWithoutMarker(root, scribeTestsProject);
                WriteFile(root, "tools/StrataLint.Scribe/DocumentEmitter.cs", "// candidate\n");
            });

        Assert.True(result.ExitCode == 0, result.Diagnostic);
        Assert.Equal([scribeTestsProject], result.SelectedProjects);
    }

    [Fact]
    public void ExecutesEachSelectedProjectWithoutFilterOrSolutionFallback()
    {
        const string scribeProject =
            "tools/StrataLint.Scribe/StrataLint.Scribe.csproj";
        const string scribeTestsProject =
            "tools/tests/StrataLint.Scribe.Tests/StrataLint.Scribe.Tests.csproj";
        var result = RunBoundary(
            root =>
            {
                WriteProject(root, scribeProject, isTest: false);
                WriteProject(root, scribeTestsProject, isTest: true, scribeProject);
                WriteFile(root, "tools/StrataLint.Scribe/DocumentEmitter.cs", "// base\n");
            },
            root => WriteFile(
                root,
                "tools/StrataLint.Scribe/DocumentEmitter.cs",
                "// candidate\n"));

        Assert.True(result.ExitCode == 0, result.Diagnostic);
        Assert.Equal([scribeTestsProject], result.SelectedProjects);
        Assert.DoesNotContain(
            result.SelectedProjects,
            static project => project.EndsWith(".sln", StringComparison.Ordinal));
    }

    private static BoundaryResult RunBoundary(
        Action<string> writeBase,
        Action<string> writeCandidate)
    {
        var root = TemporaryFileSystem.Directory.CreateTempSubdirectory(
            "stratalint-engineering-scope-").FullName;
        var originalFull = Environment.GetEnvironmentVariable("FULL");
        var originalOutput = Console.Out;
        var originalError = Console.Error;
        try
        {
            RunGit(root, "init", "--quiet");
            RunGit(root, "config", "user.email", "engineering-scope@example.invalid");
            RunGit(root, "config", "user.name", "Engineering Scope Tests");
            writeBase(root);
            RunGit(root, "add", ".");
            RunGit(root, "commit", "--quiet", "-m", "base");
            writeCandidate(root);
            RunGit(root, "add", ".");
            RunGit(root, "commit", "--quiet", "-m", "candidate");

            Environment.SetEnvironmentVariable("FULL", null);

            var head = GitText(root, "rev-parse", "HEAD");
            var @base = GitText(root, "rev-parse", "HEAD^1");
            using var output = new StringWriter { NewLine = "\n" };
            using var error = new StringWriter { NewLine = "\n" };
            Console.SetOut(output);
            Console.SetError(error);
            var exitCode = Program.Run(
                [
                    "--repository", root,
                    "--head", head,
                    "--base", @base,
                ],
                TestResultEvidence.Load,
                output,
                error);
            var selectedProjects = output.ToString()
                .Split('\n', StringSplitOptions.RemoveEmptyEntries)
                .Where(static line => line.StartsWith(
                    "ENGINEERING_TEST_PROJECT project=",
                    StringComparison.Ordinal))
                .Select(static line => JsonSerializer.Deserialize<string>(
                    line["ENGINEERING_TEST_PROJECT project=".Length..])!)
                .ToArray();
            return new BoundaryResult(
                exitCode,
                selectedProjects,
                output.ToString(),
                error.ToString());
        }
        finally
        {
            Console.SetOut(originalOutput);
            Console.SetError(originalError);
            Environment.SetEnvironmentVariable("FULL", originalFull);
            TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }

    private static void WriteProject(
        string root,
        string path,
        bool isTest,
        params string[] references)
    {
        var directory = Path.GetDirectoryName(path)!;
        var projectReferences = string.Join(
            "",
            references.Select(reference =>
                $"<ProjectReference Include=\"{Path.GetRelativePath(directory, reference).Replace('\\', '/')}\" />"));
        var testPackages = isTest
            ? """
              <PackageReference Include="Microsoft.NET.Test.Sdk" Version="18.0.1" />
              <PackageReference Include="xunit" Version="2.9.3" />
              <PackageReference Include="xunit.runner.visualstudio" Version="3.1.4" />
              """
            : "";
        WriteFile(root, path, $"""
            <Project Sdk="Microsoft.NET.Sdk">
              <PropertyGroup>
                <TargetFramework>net10.0</TargetFramework>
                <IsTestProject>{isTest.ToString().ToLowerInvariant()}</IsTestProject>
              </PropertyGroup>
              <ItemGroup>{projectReferences}{testPackages}</ItemGroup>
            </Project>
            """);
        if (isTest)
        {
            WriteFile(
                root,
                Path.Combine(directory, "SmokeTests.cs"),
                "using Xunit; public sealed class SmokeTests { [Fact] public void Runs() { } }\n");
        }
    }

    private static void WriteRunnableTestProjectWithoutMarker(
        string root,
        string path,
        params string[] references)
    {
        var directory = Path.GetDirectoryName(path)!;
        var projectReferences = string.Join(
            "",
            references.Select(reference =>
                $"<ProjectReference Include=\"{Path.GetRelativePath(directory, reference).Replace('\\', '/')}\" />"));
        WriteFile(root, path, $"""
            <Project Sdk="Microsoft.NET.Sdk">
              <PropertyGroup><TargetFramework>net10.0</TargetFramework></PropertyGroup>
              <ItemGroup>
                {projectReferences}
                <PackageReference Include="Microsoft.NET.Test.Sdk" Version="18.0.1" />
                <PackageReference Include="xunit" Version="2.9.3" />
                <PackageReference Include="xunit.runner.visualstudio" Version="3.1.4" />
              </ItemGroup>
            </Project>
            """);
        WriteFile(
            root,
            Path.Combine(directory, "SmokeTests.cs"),
            "using Xunit; public sealed class SmokeTests { [Fact] public void Runs() { } }\n");
    }

    private static void WriteFile(string root, string path, string content)
    {
        var fullPath = Path.Combine(root, path);
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
        TemporaryFileSystem.File.WriteAllText(fullPath, content);
    }

    private static string GitText(string root, params string[] arguments) =>
        RunGit(root, arguments).Trim();

    private static string RunGit(string root, params string[] arguments)
    {
        var startInfo = new ProcessStartInfo
        {
            FileName = "git",
            WorkingDirectory = root,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        foreach (var argument in arguments) startInfo.ArgumentList.Add(argument);
        using var process = Process.Start(startInfo)
            ?? throw new InvalidOperationException("could not start git");
        var output = process.StandardOutput.ReadToEnd();
        var error = process.StandardError.ReadToEnd();
        process.WaitForExit();
        if (process.ExitCode != 0)
        {
            throw new InvalidOperationException(
                $"git {string.Join(' ', arguments)} failed ({process.ExitCode}): {error}");
        }

        return output;
    }

    private sealed record BoundaryResult(
        int ExitCode,
        string[] SelectedProjects,
        string Output,
        string Error)
    {
        internal string Diagnostic =>
            $"exit={ExitCode}; selected=[{string.Join(", ", SelectedProjects)}]; "
            + $"stdout={Output}; stderr={Error}";
    }
}

[CollectionDefinition("Engineering scope process boundary", DisableParallelization = true)]
public sealed class EngineeringScopeProcessBoundaryCollection;
