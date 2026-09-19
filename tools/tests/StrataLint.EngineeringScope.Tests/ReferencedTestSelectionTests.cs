using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class ReferencedTestSelectionTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ExplicitTestRootsExecuteWhileReferenceClosureOnlySuppliesBuildMaterials(bool both)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(both ? ["filemap", "lean"] : ["filemap"]);
        const string foo = ResourceRouteTests.ResourceFixture.Foo;
        const string bar = ResourceRouteTests.ResourceFixture.Bar;
        fixture.Write(foo, """
            <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
            <OutputType>Exe</OutputType></PropertyGroup><ItemGroup><ProjectReference Include="../Bar/Bar.csproj" /></ItemGroup></Project>
            """);
        fixture.Write("tools/Foo/Program.cs", "System.Console.WriteLine(BarValue.Read());\n");
        fixture.Write("tools/Bar/Program.cs", "System.Console.WriteLine(BarValue.Read()); public static class BarValue { public static int Read() => 17; }\n");
        fixture.Write(EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Manifest(
            new EngineeringProjectFixture(foo, "Foo", "cross-cutting-test", true, ["tools/Foo/Program.cs"], References: [bar]),
            new EngineeringProjectFixture(bar, "Bar", "cross-cutting-test", true, ["tools/Bar/Program.cs"])));
        fixture.CommitPlan();
        var expected = (both ? new[] { foo, bar } : [foo]).Order(StringComparer.Ordinal).ToArray();
        Assert.Equal(expected, ResourceExecutionPlan.Load(fixture.Root, fixture.Plan, fixture.Changes)!.Projects);
        using var output = new StringWriter();
        Assert.True(fixture.Run("build", output) == 0, output.ToString());
        var build = CommonExecutionEvidence.ValidateBuild(fixture.Root);
        Assert.Contains(build.Materials, material => material.Path.EndsWith("/Bar.dll", StringComparison.Ordinal));
        Assert.Equal(expected, CommonBuildOutputs.TestAssemblies(fixture.Root, build).Keys.Order(StringComparer.Ordinal));
        var calls = new List<string>();
        Assert.True(Program.RunCurrentTests(fixture.Root, (project, results) =>
        {
            calls.Add(project);
            Directory.CreateDirectory(results);
            var assembly = Path.GetFileNameWithoutExtension(project);
            File.WriteAllText(Path.Combine(results, "execution.trx"), $$"""
                <TestRun><Results><UnitTestResult testId="one" testName="Fixture.Runs" outcome="Passed" /></Results>
                <TestDefinitions><UnitTest id="one" storage="{{assembly}}.dll"><TestMethod className="Fixture" name="Runs" /></UnitTest></TestDefinitions>
                <ResultSummary outcome="Completed"><Counters executed="1" passed="1" failed="0" /></ResultSummary></TestRun>
                """);
            return 0;
        }, output, build) == 0, output.ToString());
        Assert.Equal(expected, calls.Order(StringComparer.Ordinal));
        Assert.Equal(expected, CommonExecutionEvidence.ValidateTests(fixture.Root).Projects.Select(project => project.Project));
    }
}
