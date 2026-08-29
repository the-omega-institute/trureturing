using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class EngineeringScopeHarnessTests
{
    [Fact]
    public void BaseOwnedIdentityDeletedWithoutDeclarationFailsClosed()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var repository = CreateIdentityRepository(fixture.Path);
        DeleteLegacyTest(repository);
        var head = GitText(repository, "rev-parse", "HEAD");
        var @base = GitText(repository, "rev-parse", "HEAD^1");
        var planFile = Path.Combine(fixture.Path, "plan.json");

        var plan = RunEngineeringScopeMode(
            TestRepositoryLayout.FindRoot(), repository, planFile, head, @base, "plan", "FULL=1");
        Assert.Equal(0, plan.ExitCode);

        var execute = RunEngineeringScope(
            TestRepositoryLayout.FindRoot(), repository, planFile, head, @base);
        var output = Encoding.UTF8.GetString(execute.StandardOutput)
            + Encoding.UTF8.GetString(execute.StandardError);

        Assert.Equal(1, execute.ExitCode);
        Assert.Contains(
            "TRX is missing base-owned tests: Probe.Tests::IdentityProbe.Legacy",
            output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void SchemaValidEmptyFullArtifactTriggersBaseOwnedReplanBeforeExecution()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var repository = CreateIdentityRepository(fixture.Path);
        DeleteLegacyTest(repository);
        var head = GitText(repository, "rev-parse", "HEAD");
        var @base = GitText(repository, "rev-parse", "HEAD^1");
        var planFile = Path.Combine(fixture.Path, "plan.json");
        var plan = RunEngineeringScopeMode(
            TestRepositoryLayout.FindRoot(), repository, planFile, head, @base, "plan", "FULL=1");
        Assert.Equal(0, plan.ExitCode);
        RewriteFullPlanTests(planFile, static _ => false);

        var execute = RunEngineeringScope(
            TestRepositoryLayout.FindRoot(), repository, planFile, head, @base);
        var output = Encoding.UTF8.GetString(execute.StandardOutput)
            + Encoding.UTF8.GetString(execute.StandardError);

        Assert.Equal(1, execute.ExitCode);
        Assert.Contains("ENGINEERING_TEST_PLAN_FALLBACK", output, StringComparison.Ordinal);
        Assert.Contains(
            "TRX is missing base-owned tests: Probe.Tests::IdentityProbe.Legacy",
            output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void SchemaValidTruncatedFullArtifactTriggersBaseOwnedReplanBeforeExecution()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var repository = CreateIdentityRepository(fixture.Path);
        DeleteLegacyTest(repository);
        var head = GitText(repository, "rev-parse", "HEAD");
        var @base = GitText(repository, "rev-parse", "HEAD^1");
        var planFile = Path.Combine(fixture.Path, "plan.json");
        var plan = RunEngineeringScopeMode(
            TestRepositoryLayout.FindRoot(), repository, planFile, head, @base, "plan", "FULL=1");
        Assert.Equal(0, plan.ExitCode);
        RewriteFullPlanTests(
            planFile,
            static test => test["id"]!.GetValue<string>() == "IdentityProbe.Survivor");

        var execute = RunEngineeringScope(
            TestRepositoryLayout.FindRoot(), repository, planFile, head, @base);
        var output = Encoding.UTF8.GetString(execute.StandardOutput)
            + Encoding.UTF8.GetString(execute.StandardError);

        Assert.Equal(1, execute.ExitCode);
        Assert.Contains("ENGINEERING_TEST_PLAN_FALLBACK", output, StringComparison.Ordinal);
        Assert.Contains(
            "TRX is missing base-owned tests: Probe.Tests::IdentityProbe.Legacy",
            output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void ExplicitRetirementLetsLegitimateDeletionPassAndNamesItsDeclaration()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var repository = CreateIdentityRepository(fixture.Path);
        DeleteLegacyTest(repository, declaration: "retired");
        var head = GitText(repository, "rev-parse", "HEAD");
        var @base = GitText(repository, "rev-parse", "HEAD^1");
        var planFile = Path.Combine(fixture.Path, "plan.json");

        var plan = RunEngineeringScopeMode(
            TestRepositoryLayout.FindRoot(), repository, planFile, head, @base, "plan", "FULL=1");
        Assert.Equal(0, plan.ExitCode);

        var execute = RunEngineeringScope(
            TestRepositoryLayout.FindRoot(), repository, planFile, head, @base);
        var output = Encoding.UTF8.GetString(execute.StandardOutput)
            + Encoding.UTF8.GetString(execute.StandardError);

        Assert.True(execute.ExitCode == 0, output);
        Assert.Contains(
            "ENGINEERING_TEST_IDENTITY_REMOVED base=\"Probe.Tests::IdentityProbe.Legacy\" disposition=retired",
            output,
            StringComparison.Ordinal);
        Assert.Contains(
            "declaration=\"Golden/EngineeringTestRetirements/identity-probe-legacy.json\"",
            output,
            StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("renamed")]
    [InlineData("moved")]
    public void ExplicitReplacementLetsLegitimateIdentityChangePass(string disposition)
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var repository = CreateIdentityRepository(fixture.Path);
        var moved = disposition == "moved";
        if (moved)
        {
            WriteMovedTestProject(repository);
        }

        DeleteLegacyTest(
            repository,
            declaration: disposition,
            replacement: moved ? "IdentityProbe.Legacy" : "IdentityProbe.Replacement",
            replacementAssembly: moved ? "Probe.Moved.Tests" : "Probe.Tests",
            addReplacementMethod: !moved);
        var head = GitText(repository, "rev-parse", "HEAD");
        var @base = GitText(repository, "rev-parse", "HEAD^1");
        var planFile = Path.Combine(fixture.Path, "plan.json");

        var plan = RunEngineeringScopeMode(
            TestRepositoryLayout.FindRoot(), repository, planFile, head, @base, "plan", "FULL=1");
        Assert.Equal(0, plan.ExitCode);

        var execute = RunEngineeringScope(
            TestRepositoryLayout.FindRoot(), repository, planFile, head, @base);
        var output = Encoding.UTF8.GetString(execute.StandardOutput)
            + Encoding.UTF8.GetString(execute.StandardError);

        Assert.True(execute.ExitCode == 0, output);
        Assert.Contains($"disposition={disposition}", output, StringComparison.Ordinal);
        Assert.Contains(
            moved
                ? "replacement=\"Probe.Moved.Tests::IdentityProbe.Legacy\""
                : "replacement=\"Probe.Tests::IdentityProbe.Replacement\"",
            output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void UnchangedRetirementDeclarationCannotAuthorizeLaterDeletion()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var repository = CreateIdentityRepository(fixture.Path);
        WriteRetirementDeclaration(repository, "retired", replacement: null);
        Git(repository, "add", ".");
        Git(repository, "commit", "--quiet", "-m", "predeclare retirement");
        DeleteLegacyTest(repository);
        var head = GitText(repository, "rev-parse", "HEAD");
        var @base = GitText(repository, "rev-parse", "HEAD^1");
        var planFile = Path.Combine(fixture.Path, "plan.json");

        var plan = RunEngineeringScopeMode(
            TestRepositoryLayout.FindRoot(), repository, planFile, head, @base, "plan", "FULL=1");
        Assert.Equal(0, plan.ExitCode);
        var execute = RunEngineeringScope(
            TestRepositoryLayout.FindRoot(), repository, planFile, head, @base);
        var output = Encoding.UTF8.GetString(execute.StandardOutput)
            + Encoding.UTF8.GetString(execute.StandardError);

        Assert.Equal(1, execute.ExitCode);
        Assert.Contains(
            "TRX is missing base-owned tests: Probe.Tests::IdentityProbe.Legacy",
            output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void DeclaredReplacementMustActuallyExecute()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var repository = CreateIdentityRepository(fixture.Path);
        DeleteLegacyTest(
            repository,
            declaration: "renamed",
            replacement: "IdentityProbe.Replacement",
            addReplacementMethod: false);
        var head = GitText(repository, "rev-parse", "HEAD");
        var @base = GitText(repository, "rev-parse", "HEAD^1");
        var planFile = Path.Combine(fixture.Path, "plan.json");

        var plan = RunEngineeringScopeMode(
            TestRepositoryLayout.FindRoot(), repository, planFile, head, @base, "plan", "FULL=1");
        Assert.Equal(0, plan.ExitCode);
        var execute = RunEngineeringScope(
            TestRepositoryLayout.FindRoot(), repository, planFile, head, @base);
        var output = Encoding.UTF8.GetString(execute.StandardOutput)
            + Encoding.UTF8.GetString(execute.StandardError);

        Assert.Equal(1, execute.ExitCode);
        Assert.Contains(
            "declared test replacement is missing from TRX: Probe.Tests::IdentityProbe.Replacement",
            output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void BaseBaselineDiscoversArbitrarilyNamedXunitProjectWithoutHarnessList()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var repository = CreateIdentityRepository(fixture.Path, "Fourth.Project", "Fourth.Tests");
        var identities = Enumerable.Range(0, 12)
            .Select(static index => $"IdentityProbe.Baseline{index:D2}")
            .ToArray();
        var methods = string.Join(
            ' ',
            identities.Select(static identity => $"[Fact] public void {identity.Split('.').Last()}() {{ }}"));
        File.WriteAllText(
            Path.Combine(repository, "tools", "tests", "Fourth.Project", "IdentityProbe.cs"),
            $"using Xunit; public sealed class IdentityProbe {{ {methods} }}\n");
        Git(repository, "add", ".");
        Git(repository, "commit", "--quiet", "--amend", "--no-edit");
        File.AppendAllText(Path.Combine(repository, "README.md"), "candidate\n");
        Git(repository, "add", "README.md");
        Git(repository, "commit", "--quiet", "-m", "candidate");
        var head = GitText(repository, "rev-parse", "HEAD");
        var @base = GitText(repository, "rev-parse", "HEAD^1");
        var planFile = Path.Combine(fixture.Path, "plan.json");

        var result = RunEngineeringScopeMode(
            TestRepositoryLayout.FindRoot(), repository, planFile, head, @base, "plan", "FULL=1");

        Assert.Equal(0, result.ExitCode);
        using var artifact = JsonDocument.Parse(ReadTemporaryText(planFile));
        var tests = artifact.RootElement.GetProperty("plan").GetProperty("tests")
            .EnumerateArray()
            .Select(static test => $"{test.GetProperty("assembly").GetString()}::{test.GetProperty("id").GetString()}")
            .ToArray();
        Assert.Equal(identities.Select(static identity => $"Fourth.Tests::{identity}"), tests);
    }

    [Fact]
    public void BaseBaselineExcludesStaticallySkippedTestsAndRetainsRunnableTests()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var repository = CreateIdentityRepository(fixture.Path);
        File.WriteAllText(
            Path.Combine(repository, "tools", "tests", "Probe", "IdentityProbe.cs"),
            "using Xunit; public sealed class IdentityProbe { [Fact] public void Runnable() { } [Fact(Skip = \"fixture\")] public void Disabled() { } }\n");
        Git(repository, "add", ".");
        Git(repository, "commit", "--quiet", "--amend", "--no-edit");
        File.AppendAllText(Path.Combine(repository, "README.md"), "candidate\n");
        Git(repository, "add", "README.md");
        Git(repository, "commit", "--quiet", "-m", "candidate");
        var head = GitText(repository, "rev-parse", "HEAD");
        var @base = GitText(repository, "rev-parse", "HEAD^1");
        var planFile = Path.Combine(fixture.Path, "plan.json");

        var result = RunEngineeringScopeMode(
            TestRepositoryLayout.FindRoot(), repository, planFile, head, @base, "plan", "FULL=1");

        Assert.Equal(0, result.ExitCode);
        using var artifact = JsonDocument.Parse(ReadTemporaryText(planFile));
        var tests = artifact.RootElement.GetProperty("plan").GetProperty("tests")
            .EnumerateArray()
            .Select(static test => $"{test.GetProperty("assembly").GetString()}::{test.GetProperty("id").GetString()}")
            .ToArray();
        Assert.Equal(["Probe.Tests::IdentityProbe.Runnable"], tests);
    }

    [Fact]
    public void EngineeringScopeRejectsAncestorThatIsNotHeadFirstParent()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var repository = CreateIdentityRepository(fixture.Path);
        var grandparent = GitText(repository, "rev-parse", "HEAD");
        File.AppendAllText(Path.Combine(repository, "README.md"), "middle\n");
        Git(repository, "add", "README.md");
        Git(repository, "commit", "--quiet", "-m", "middle");
        File.AppendAllText(Path.Combine(repository, "README.md"), "head\n");
        Git(repository, "add", "README.md");
        Git(repository, "commit", "--quiet", "-m", "head");
        var head = GitText(repository, "rev-parse", "HEAD");

        var result = RunEngineeringScopeMode(
            TestRepositoryLayout.FindRoot(),
            repository,
            Path.Combine(fixture.Path, "plan.json"),
            head,
            grandparent,
            "plan");
        var error = Encoding.UTF8.GetString(result.StandardError);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("--base must equal the checked HEAD^1", error, StringComparison.Ordinal);
    }

    private static void RewriteFullPlanTests(
        string planFile,
        Func<JsonObject, bool> retain)
    {
        var artifact = JsonNode.Parse(ReadTemporaryText(planFile))!.AsObject();
        var plan = artifact["plan"]!.AsObject();
        Assert.Equal("full", plan["kind"]!.GetValue<string>());
        var retained = plan["tests"]!.AsArray()
            .Select(static test => test!.AsObject())
            .Where(retain)
            .Select(static test => test.DeepClone())
            .ToArray();
        plan["tests"] = new JsonArray(retained);
        File.WriteAllText(
            planFile,
            artifact.ToJsonString(new JsonSerializerOptions { WriteIndented = true }) + "\n");
    }

    [Fact]
    public void RetirementDeclarationRejectsUnknownJsonMembers()
    {
        using var fixture = new TemporaryDirectory();
        const string path = "Golden/EngineeringTestRetirements/unknown-member.json";
        WriteRawRetirement(
            fixture.Path,
            path,
            "{\"schema_version\":1,\"assembly\":\"Probe.Tests\",\"id\":\"IdentityProbe.Legacy\",\"disposition\":\"retired\",\"replacement\":null,\"reason\":\"fixture\",\"unknown\":true}\n");

        Assert.Throws<JsonException>(() => EngineeringTestRetirementLoader.Load(
            fixture.Path,
            [path],
            ExpectedLegacyTest()));
    }

    [Theory]
    [InlineData("retired", "{\"assembly\":\"Probe.Tests\",\"id\":\"IdentityProbe.Replacement\"}")]
    [InlineData("renamed", "null")]
    [InlineData("moved", "null")]
    public void RetirementDeclarationDispositionAndReplacementMustAgree(
        string disposition,
        string replacement)
    {
        using var fixture = new TemporaryDirectory();
        const string path = "Golden/EngineeringTestRetirements/invalid-shape.json";
        WriteRawRetirement(
            fixture.Path,
            path,
            $"{{\"schema_version\":1,\"assembly\":\"Probe.Tests\",\"id\":\"IdentityProbe.Legacy\",\"disposition\":\"{disposition}\",\"replacement\":{replacement},\"reason\":\"fixture\"}}\n");

        Assert.Throws<InvalidDataException>(() => EngineeringTestRetirementLoader.Load(
            fixture.Path,
            [path],
            ExpectedLegacyTest()));
    }

    [Fact]
    public void RetirementDeclarationMustAddressAPlannedBaseIdentity()
    {
        using var fixture = new TemporaryDirectory();
        const string path = "Golden/EngineeringTestRetirements/wrong-base.json";
        WriteRawRetirement(
            fixture.Path,
            path,
            "{\"schema_version\":1,\"assembly\":\"Probe.Tests\",\"id\":\"IdentityProbe.Other\",\"disposition\":\"retired\",\"replacement\":null,\"reason\":\"fixture\"}\n");

        Assert.Throws<InvalidDataException>(() => EngineeringTestRetirementLoader.Load(
            fixture.Path,
            [path],
            ExpectedLegacyTest()));
    }

    private static string CreateIdentityRepository(
        string fixtureRoot,
        string projectDirectory = "Probe",
        string assembly = "Probe.Tests")
    {
        var repository = Path.Combine(fixtureRoot, "candidate");
        var directory = Path.Combine(repository, "tools", "tests", projectDirectory);
        Directory.CreateDirectory(directory);
        File.WriteAllText(Path.Combine(repository, "README.md"), "base\n");
        File.WriteAllText(
            Path.Combine(directory, $"{projectDirectory}.csproj"),
            $"""
            <Project Sdk="Microsoft.NET.Sdk">
              <PropertyGroup><TargetFramework>net10.0</TargetFramework><IsTestProject>true</IsTestProject><AssemblyName>{assembly}</AssemblyName><RestorePackagesWithLockFile>false</RestorePackagesWithLockFile></PropertyGroup>
              <ItemGroup><PackageReference Include="Microsoft.NET.Test.Sdk" Version="18.0.1" /><PackageReference Include="xunit" Version="2.9.3" /><PackageReference Include="xunit.runner.visualstudio" Version="3.1.4" /></ItemGroup>
            </Project>
            """);
        File.WriteAllText(
            Path.Combine(directory, "IdentityProbe.cs"),
            "using Xunit; public sealed class IdentityProbe { [Fact] public void Legacy() { } [Fact] public void Survivor() { } }\n");
        Directory.CreateDirectory(Path.Combine(repository, "tools"));
        File.WriteAllText(
            Path.Combine(repository, "tools", "StrataLint.sln"),
            $$"""
            Microsoft Visual Studio Solution File, Format Version 12.00
            # Visual Studio Version 17
            Project("{FAE04EC0-301F-11D3-BF4B-00C04F79EFBC}") = "{{projectDirectory}}", "tests/{{projectDirectory}}/{{projectDirectory}}.csproj", "{BD700716-FC67-411D-B4E4-5F8C0A552E7B}"
            EndProject
            Global
                GlobalSection(SolutionConfigurationPlatforms) = preSolution
                    Release|Any CPU = Release|Any CPU
                EndGlobalSection
                GlobalSection(ProjectConfigurationPlatforms) = postSolution
                    {BD700716-FC67-411D-B4E4-5F8C0A552E7B}.Release|Any CPU.ActiveCfg = Release|Any CPU
                    {BD700716-FC67-411D-B4E4-5F8C0A552E7B}.Release|Any CPU.Build.0 = Release|Any CPU
                EndGlobalSection
            EndGlobal
            """);
        Git(repository, "init", "--quiet");
        Git(repository, "config", "user.email", "engineering-identity@example.invalid");
        Git(repository, "config", "user.name", "engineering-identity");
        Git(repository, "add", ".");
        Git(repository, "commit", "--quiet", "-m", "base");
        return repository;
    }

    private static void DeleteLegacyTest(
        string repository,
        string? declaration = null,
        string? replacement = null,
        string replacementAssembly = "Probe.Tests",
        bool addReplacementMethod = true)
    {
        var source = Path.Combine(
            repository,
            "tools",
            "tests",
            "Probe",
            "IdentityProbe.cs");
        var replacementMethod = replacement is null || !addReplacementMethod
            ? string.Empty
            : " [Fact] public void Replacement() { }";
        File.WriteAllText(
            source,
            $"using Xunit; public sealed class IdentityProbe {{ [Fact] public void Survivor() {{ }}{replacementMethod} }}\n");
        if (declaration is not null)
        {
            WriteRetirementDeclaration(repository, declaration, replacement, replacementAssembly);
        }

        Git(repository, "add", ".");
        Git(repository, "commit", "--quiet", "-m", "delete legacy test");
    }

    private static void WriteRetirementDeclaration(
        string repository,
        string disposition,
        string? replacement,
        string replacementAssembly = "Probe.Tests")
    {
        var directory = Path.Combine(repository, "Golden", "EngineeringTestRetirements");
        Directory.CreateDirectory(directory);
        var replacementJson = replacement is null
            ? "null"
            : $"{{\"assembly\":\"{replacementAssembly}\",\"id\":\"{replacement}\"}}";
        File.WriteAllText(
            Path.Combine(directory, "identity-probe-legacy.json"),
            $"{{\"schema_version\":1,\"assembly\":\"Probe.Tests\",\"id\":\"IdentityProbe.Legacy\",\"disposition\":\"{disposition}\",\"replacement\":{replacementJson},\"reason\":\"fixture identity change\"}}\n");
    }

    private static void WriteMovedTestProject(string repository)
    {
        var directory = Path.Combine(repository, "tools", "tests", "MovedProbe");
        Directory.CreateDirectory(directory);
        File.WriteAllText(
            Path.Combine(directory, "MovedProbe.csproj"),
            """
            <Project Sdk="Microsoft.NET.Sdk">
              <PropertyGroup><TargetFramework>net10.0</TargetFramework><IsTestProject>true</IsTestProject><AssemblyName>Probe.Moved.Tests</AssemblyName><RestorePackagesWithLockFile>false</RestorePackagesWithLockFile></PropertyGroup>
              <ItemGroup><PackageReference Include="Microsoft.NET.Test.Sdk" Version="18.0.1" /><PackageReference Include="xunit" Version="2.9.3" /><PackageReference Include="xunit.runner.visualstudio" Version="3.1.4" /></ItemGroup>
            </Project>
            """);
        File.WriteAllText(
            Path.Combine(directory, "IdentityProbe.cs"),
            "using Xunit; public sealed class IdentityProbe { [Fact] public void Legacy() { } }\n");

        File.WriteAllText(
            Path.Combine(repository, "tools", "StrataLint.sln"),
            """
            Microsoft Visual Studio Solution File, Format Version 12.00
            # Visual Studio Version 17
            Project("{FAE04EC0-301F-11D3-BF4B-00C04F79EFBC}") = "Probe", "tests/Probe/Probe.csproj", "{BD700716-FC67-411D-B4E4-5F8C0A552E7B}"
            EndProject
            Project("{FAE04EC0-301F-11D3-BF4B-00C04F79EFBC}") = "MovedProbe", "tests/MovedProbe/MovedProbe.csproj", "{02A480B4-AB06-4DC0-9656-A95F54C10119}"
            EndProject
            Global
                GlobalSection(SolutionConfigurationPlatforms) = preSolution
                    Release|Any CPU = Release|Any CPU
                EndGlobalSection
                GlobalSection(ProjectConfigurationPlatforms) = postSolution
                    {BD700716-FC67-411D-B4E4-5F8C0A552E7B}.Release|Any CPU.ActiveCfg = Release|Any CPU
                    {BD700716-FC67-411D-B4E4-5F8C0A552E7B}.Release|Any CPU.Build.0 = Release|Any CPU
                    {02A480B4-AB06-4DC0-9656-A95F54C10119}.Release|Any CPU.ActiveCfg = Release|Any CPU
                    {02A480B4-AB06-4DC0-9656-A95F54C10119}.Release|Any CPU.Build.0 = Release|Any CPU
                EndGlobalSection
            EndGlobal
            """);
    }

    private static EngineeringSelectedTest[] ExpectedLegacyTest() =>
    [
        new(
            "tools/tests/Probe/Probe.csproj",
            "IdentityProbe.Legacy",
            EngineeringSelectedTestReason.BaseBaseline,
            "fixture",
            "Probe.Tests"),
    ];

    private static void WriteRawRetirement(string repository, string path, string content)
    {
        var fullPath = Path.Combine(repository, path.Replace('/', Path.DirectorySeparatorChar));
        Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
        File.WriteAllText(fullPath, content);
    }
}
