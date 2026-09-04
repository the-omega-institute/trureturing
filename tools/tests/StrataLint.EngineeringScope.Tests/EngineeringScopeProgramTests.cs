using System.Diagnostics;
using System.Security.Cryptography;
using System.Text;
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
    private const string ScriptTestsProject =
        "tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj";

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
        Assert.Equal(2, result.RetryCount);
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
    public void FullOverrideSkipsGateDerivationWhenCandidateControllerInputIsMissing()
    {
        const string missingRuntimeInput = "tools/scripts/report/report-supervisor.sh";
        var result = RunBoundary(
            static _ => { },
            root => TemporaryFileSystem.File.Delete(Path.Combine(root, missingRuntimeInput)),
            full: true);

        Assert.True(result.ExitCode == 0, result.Diagnostic);
        Assert.Contains(ScriptTestsProject, result.SelectedProjects);
        Assert.Contains("ENGINEERING_TEST_PLAN state=full", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void MissingBuildOutputRetriesOnce() =>
        AssertRunTestsScenario(
            "RunsAfterFallback", "Assert.True(true);", prebuild: false, expectedExitCode: 0, expectedRetryCount: 1);

    [Fact]
    public void PrebuiltTestProjectDoesNotRetry() =>
        AssertRunTestsScenario(
            "RunsPrebuilt", "Assert.True(true);", prebuild: true, expectedExitCode: 0, expectedRetryCount: 0);

    [Fact]
    public void RealTestFailureDoesNotRetry() =>
        AssertRunTestsScenario(
            "Fails", "Assert.True(false, \"intentional\");", prebuild: true, expectedExitCode: 1, expectedRetryCount: 0);

    [Fact]
    public void ConfiguredEvidenceDirectoryRetainsTrxAfterExecution()
    {
        var evidence = TemporaryFileSystem.Directory.CreateTempSubdirectory(
            "stratalint-engineering-evidence-").FullName;
        var projectDirectory = Path.Combine(
            evidence,
            Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(ProductTestsProject)))
                .ToLowerInvariant());
        var original = Environment.GetEnvironmentVariable("ENGINEERING_TRX_DIRECTORY");
        try
        {
            Environment.SetEnvironmentVariable("ENGINEERING_TRX_DIRECTORY", evidence);
            var result = RunBoundary(
                WriteProductProjects,
                root => WriteSmokeTest(root, "ExportsEvidence", "Assert.True(true);"));

            Assert.True(result.ExitCode == 0, result.Diagnostic);
            Assert.NotEmpty(Directory.GetFiles(projectDirectory, "*.trx", SearchOption.TopDirectoryOnly));
        }
        finally
        {
            Environment.SetEnvironmentVariable("ENGINEERING_TRX_DIRECTORY", original);
            TemporaryFileSystem.Directory.Delete(evidence, recursive: true);
        }
    }

    private static void AssertRunTestsScenario(
        string testName,
        string testBody,
        bool prebuild,
        int expectedExitCode,
        int expectedRetryCount)
    {
        var result = RunBoundary(
            WriteProductProjects,
            root => WriteSmokeTest(root, testName, testBody),
            prebuild
                ? root => RunDotNet(
                    root, "build", ProductTestsProject, "--configuration", "Release", "--nologo")
                : null);

        Assert.True(result.ExitCode == expectedExitCode, result.Diagnostic);
        Assert.Equal([ProductTestsProject], result.SelectedProjects);
        Assert.Equal(expectedRetryCount, result.RetryCount);
    }

    private static BoundaryResult RunBoundary(
        Action<string> writeBase,
        Action<string> writeCandidate,
        Action<string>? prepareExecution = null,
        bool full = false)
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
            WriteGateInfrastructure(root);
            writeBase(root);
            RunGit(root, "add", ".");
            RunGit(root, "commit", "--quiet", "-m", "base");
            writeCandidate(root);
            RunGit(root, "add", ".");
            RunGit(root, "commit", "--quiet", "-m", "candidate");
            prepareExecution?.Invoke(root);

            Environment.SetEnvironmentVariable("FULL", full ? "1" : null);

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

    private static void WriteSmokeTest(string root, string name, string body) =>
        WriteFile(
            root,
            Path.Combine(Path.GetDirectoryName(ProductTestsProject)!, "SmokeTests.cs"),
            $"using Xunit; public sealed class SmokeTests {{ [Fact] public void {name}() {{ {body} }} }}\n");

    private static void WriteProductProjects(string root)
    {
        WriteProject(root, ProductProject, isTest: false);
        WriteProject(root, ProductTestsProject, isTest: true, ProductProject);
    }

    private static void WriteGateInfrastructure(string root)
    {
        WriteProject(root, ScriptTestsProject, isTest: true);
        WriteFile(
            root,
            "tools/tests/StrataLint.ScriptTests/packages.lock.json",
            """
            {
              "version": 2,
              "dependencies": {
                "net10.0": {
                  "xunit.assert": { "type": "Transitive", "resolved": "2.9.3" },
                  "xunit.extensibility.core": { "type": "Transitive", "resolved": "2.9.3" }
                }
              }
            }

            """);
        WriteProject(
            root,
            "tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj",
            isTest: false);
        WriteFile(root, "Directory.Build.props", "<Project />\n");
        WriteFile(root, "Directory.Packages.props", "<Project />\n");
        WriteFile(root, "tools/scripts/workflow/self-lock-probe.sh", "exit 0\n");
        WriteFile(root, "tools/scripts/report/report-supervisor.sh", "exit 0\n");
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
        => RunProcess("git", root, arguments);

    private static string RunDotNet(string root, params string[] arguments)
        => RunProcess("dotnet", root, arguments);

    private static string RunProcess(string fileName, string root, params string[] arguments)
    {
        var startInfo = new ProcessStartInfo
        {
            FileName = fileName,
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
                $"{fileName} {string.Join(' ', arguments)} failed ({process.ExitCode}): {error}");
        }

        return output;
    }

    private sealed record BoundaryResult(
        int ExitCode,
        string[] SelectedProjects,
        string Output,
        string Error)
    {
        internal int RetryCount => Output.Split('\n').Count(static line =>
            line.StartsWith("ENGINEERING_TEST_RETRY ", StringComparison.Ordinal));

        internal string Diagnostic =>
            $"exit={ExitCode}; selected=[{string.Join(", ", SelectedProjects)}]; "
            + $"stdout={Output}; stderr={Error}";
    }
}

[CollectionDefinition("Engineering scope process boundary", DisableParallelization = true)]
public sealed class EngineeringScopeProcessBoundaryCollection;
