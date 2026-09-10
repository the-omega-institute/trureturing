using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class AffectedBoundaryTests
{
    [Fact]
    public void UnsetLanguageSurvivesSealingExecutorAndDownstreamVerification()
    {
        var previous = Environment.GetEnvironmentVariable("DOTNET_CLI_UI_LANGUAGE");
        var culture = System.Globalization.CultureInfo.CurrentCulture;
        var uiCulture = System.Globalization.CultureInfo.CurrentUICulture;
        try
        {
            Environment.SetEnvironmentVariable("DOTNET_CLI_UI_LANGUAGE", null);
            using var fixture = new AffectedExecutionFixture();
            AffectedEnvironmentObservation.Write(fixture.Root, "fixture-after-unset");
            var child = CommonStages.TestEnvironment();
            Assert.Equal("en-US", child.UICulture);
            System.Globalization.CultureInfo.CurrentCulture = new("fr-FR");
            System.Globalization.CultureInfo.CurrentUICulture = new("tr-TR");
            Assert.Equal(child, CommonStages.TestEnvironment());
            var build = fixture.Build();
            Assert.Null(Environment.GetEnvironmentVariable("DOTNET_CLI_UI_LANGUAGE"));
            Assert.All(fixture.Plan().Actions, action => Assert.Equal(child.Identity, action.Environment));
            var cold = fixture.Tests(build, subprocess: true);
            Assert.Equal(2, cold.Projects.Sum(project => project.Executed));
            CommonExecutionEvidence.ValidateTests(fixture.Root);
            fixture.VerifyTestHostCultures(child.Culture, child.UICulture);
            var warm = fixture.Tests(build, subprocess: true);
            Assert.Equal(0, warm.Projects.Sum(project => project.Executed));
            Assert.All(warm.Projects.SelectMany(project => project.Coverage), coverage =>
            {
                Assert.Equal("reused", coverage.Status);
                Assert.Equal(cold.Round, coverage.Source.Round);
            });
            CommonExecutionEvidence.ValidateTests(fixture.Root);
            fixture.ClearSeed();
            var full = fixture.Tests(build, subprocess: true);
            Assert.Equal(2, full.Projects.Sum(project => project.Executed));
            Assert.Equal(warm.Projects.Select(project => project.Exit), full.Projects.Select(project => project.Exit));
            Assert.Equal(2, warm.Projects.SelectMany(project => project.Coverage).Sum(coverage => coverage.Covered));
        }
        finally
        {
            Environment.SetEnvironmentVariable("DOTNET_CLI_UI_LANGUAGE", previous);
            System.Globalization.CultureInfo.CurrentCulture = culture;
            System.Globalization.CultureInfo.CurrentUICulture = uiCulture;
        }
    }

    [Fact]
    public void AssemblyFrameworkContractCannotReuseSuccessAfterAmbientInputChanges()
    {
        const string variable = "AFFECTED_FRAMEWORK_INPUT";
        var previous = Environment.GetEnvironmentVariable(variable);
        try
        {
            Environment.SetEnvironmentVariable(variable, "pass");
            using var fixture = new AffectedExecutionFixture();
            fixture.Write("tools/tests/StrataLint.First/Framework.cs", """
                using System;
                using System.Reflection;
                using Xunit.Abstractions;
                using Xunit.Sdk;
                [assembly: First.FrameworkSelection]
                namespace First;
                [AttributeUsage(AttributeTargets.Assembly)]
                [TestFrameworkDiscoverer("First.FrameworkDiscoverer", "StrataLint.First")]
                public sealed class FrameworkSelectionAttribute : Attribute, ITestFrameworkAttribute { }
                public sealed class FrameworkDiscoverer : ITestFrameworkTypeDiscoverer
                {
                    public Type GetTestFrameworkType(IAttributeInfo attribute) => typeof(AmbientFramework);
                }
                public sealed class AmbientFramework : XunitTestFramework
                {
                    public AmbientFramework(IMessageSink sink) : base(sink) { }
                    protected override ITestFrameworkExecutor CreateExecutor(AssemblyName assemblyName)
                    {
                        if (Environment.GetEnvironmentVariable("AFFECTED_FRAMEWORK_INPUT") != "pass")
                            throw new InvalidOperationException("framework ambient input rejected");
                        return base.CreateExecutor(assemblyName);
                    }
                }
                """);
            var build = fixture.Build();
            Assert.Equal(2, fixture.Tests(build).Projects.Sum(project => project.Executed));
            Environment.SetEnvironmentVariable(variable, "fail");
            var incremental = fixture.Tests(build, expectedExit: null);
            fixture.ClearSeed();
            var full = fixture.Tests(build, expectedExit: 1);
            Assert.NotNull(full.Projects[0].Error);
            Assert.NotNull(incremental.Projects[0].Error);
            Assert.DoesNotContain(incremental.Projects[0].Coverage, coverage => coverage.Status == "reused");
            Assert.Equal(0, incremental.Projects[1].Executed);
            Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateTests(fixture.Root));
            Assert.Equal(incremental.Projects.Select(project => project.Exit), full.Projects.Select(project => project.Exit));
            Assert.Equal(1, full.Projects[1].Executed);
        }
        finally { Environment.SetEnvironmentVariable(variable, previous); }
    }

    [Fact]
    public void InheritedFactUsesCompleteNativeExecutionOnEveryRound()
    {
        using var fixture = new AffectedExecutionFixture();
        fixture.Write("tools/tests/StrataLint.First/Tests.cs", """
            namespace First;
            public abstract class BaseCases
            {
                [Xunit.Fact] public void Check() { Xunit.Assert.Equal(7, Shared.Value()); }
            }
            public class ConcreteCases : BaseCases { }
            """);
        var build = fixture.Build();
        var cold = fixture.Tests(build);
        Assert.Equal(2, cold.Projects.Sum(project => project.Executed));
        var warm = fixture.Tests(build);
        Assert.Equal(1, warm.Projects.Sum(project => project.Executed));
        Assert.Equal("executed", Assert.Single(warm.Projects[0].Coverage).Status);
        Assert.Equal("reused", Assert.Single(warm.Projects[1].Coverage).Status);
        var trx = TestResultEvidence.Load(Path.Combine(fixture.Root, warm.Projects[0].Results));
        Assert.Contains("First.ConcreteCases.Check", trx.MethodCounts.Keys);
        Assert.DoesNotContain("First.BaseCases.Check", trx.MethodCounts.Keys);
        CommonExecutionEvidence.ValidateTests(fixture.Root);
        var missingExecution = warm with { Projects = warm.Projects.Select(project => project with { Executed = 0 }).ToArray() };
        CommonExecutionEvidence.Write(fixture.Root, CommonExecutionEvidence.TestsPath, missingExecution);
        Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateTests(fixture.Root));
        fixture.ClearSeed();
        var full = fixture.Tests(build);
        Assert.Equal(2, full.Projects.Sum(project => project.Executed));
        Assert.Equal(warm.Projects.Select(project => project.Exit), full.Projects.Select(project => project.Exit));
    }

    [Theory]
    [InlineData("[Xunit.Fact] public async System.Threading.Tasks.Task Check() { await System.Threading.Tasks.Task.CompletedTask; }")]
    [InlineData("[Xunit.Theory] [Xunit.InlineData(7)] public void Check(int value) { Xunit.Assert.Equal(7, value); }")]
    [InlineData("[CustomFact] public void Check() { Xunit.Assert.True(true); }")]
    public void UnresolvedDiscoveryRunsTheWholeNativeProject(string test)
    {
        using var fixture = new AffectedExecutionFixture();
        fixture.Write("tools/tests/StrataLint.First/Additional.cs", "namespace First; public class Additional { " + test
            + " } public sealed class CustomFactAttribute : Xunit.FactAttribute { }");
        var build = fixture.Build();
        Assert.Equal(3, fixture.Tests(build).Projects.Sum(project => project.Executed));
        var warm = fixture.Tests(build);
        Assert.Equal(2, warm.Projects[0].Executed);
        var coverage = Assert.Single(warm.Projects[0].Coverage);
        Assert.Equal("*", coverage.Scope);
        Assert.Equal("executed", coverage.Status);
        Assert.Equal(2, coverage.Covered);
        Assert.Equal(0, warm.Projects[1].Executed);
        CommonExecutionEvidence.ValidateTests(fixture.Root);
        fixture.ClearSeed();
        var full = fixture.Tests(build);
        Assert.Equal(3, full.Projects.Sum(project => project.Executed));
        Assert.Equal(warm.Projects.Select(project => project.Exit), full.Projects.Select(project => project.Exit));
    }
}
