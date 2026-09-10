using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class AffectedNativeBoundaryTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SharedSdkSourceInExcludedProjectPreservesSelectedClassesAndDependencies(bool referenced)
    {
        using var fixture = new AffectedExecutionFixture();
        const string excluded = "tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj";
        fixture.Write(excluded, TemporaryFileSystem.File.ReadAllText(Path.Combine(fixture.Root, AffectedExecutionFixture.First)));
        fixture.Write("tools/tests/StrataLint.ScriptTests/Tests.cs", """
            public static class ExcludedDependency { public static int Value() => Shared.Value(); }
            public class ExcludedTests { [Xunit.Fact] public void MustNotRun() { Xunit.Assert.Fail("excluded from CI"); } }
            """);
        fixture.Run("dotnet", "sln", "tools/StrataLint.sln", "add", excluded);
        if (referenced)
        {
            fixture.Run("dotnet", "add", AffectedExecutionFixture.First, "reference", excluded);
            fixture.Write("tools/tests/StrataLint.First/Tests.cs", "namespace First; public class Tests { [Xunit.Fact] public void Runs() { Xunit.Assert.Equal(7, ExcludedDependency.Value()); } }\n");
        }
        fixture.Run("dotnet", "restore", "tools/StrataLint.sln", "--use-lock-file");
        var build = fixture.Build();
        var native = CommonExecutionEvidence.Read<NativeProject[]>(fixture.Root, AffectedTestPlan.NativePath);
        var sdkSource = native.Single(project => project.Project == excluded).Compile.Single(path =>
            path.EndsWith("Microsoft.NET.Test.Sdk.Program.cs", StringComparison.Ordinal));
        Assert.Equal(3, native.Count(project => project.Compile.Contains(sdkSource, StringComparer.Ordinal)));
        var plan = fixture.Plan();
        Assert.Equal(new[] { "First.Tests", "Second.Tests" }, plan.Actions.Select(action => action.Scope));
        Assert.All(plan.Actions, action => Assert.Empty(action.Unknown));
        Assert.DoesNotContain(plan.Projects, project => project.Project == excluded);
        var first = plan.Projects.Single(project => project.Project == AffectedExecutionFixture.First);
        Assert.Equal(referenced, first.Inputs.Any(input => input.Path == "compiler:" + excluded));
        Assert.Contains(first.Inputs, input => input.Path == "compile:tools/StrataLint.Shared/Value.cs");
        if (referenced)
            Assert.Contains(first.Inputs, input => input.Path.StartsWith("material:", StringComparison.Ordinal)
                && input.Path.EndsWith("/StrataLint.ScriptTests.dll", StringComparison.Ordinal));
        var executed = fixture.Tests(build);
        Assert.Equal(2, executed.Projects.Sum(project => project.Executed));
        Assert.DoesNotContain(executed.Projects, project => project.Project == excluded);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ChecksumConsistentDuplicateInputPathsAreRejected(bool actionInputs)
    {
        using var scratch = new SeedFixture();
        var valid = Manifest();
        AffectedTestPlan.Validate(valid);
        var malformed = DuplicateInputs(valid, actionInputs);
        Assert.Throws<InvalidDataException>(() => AffectedTestPlan.Validate(malformed));
        scratch.Save(malformed);
        var cache = new AffectedTestCache(scratch.Root, TextWriter.Null);
        Assert.Null(cache.Seed);
        var selection = cache.Select(valid.Actions[0], valid.Projects[0]);
        Assert.Null(selection.Success);
        Assert.StartsWith("unusable-seed:", selection.Reason, StringComparison.Ordinal);
    }

    [Fact]
    public void DiagnosticInputMapCollisionFallsBackToExecution()
    {
        using var scratch = new SeedFixture();
        // The same file can be both a native project input and a test runtime input.
        // Each map is valid; diagnostics must not abort selection when combining them.
        var plan = Manifest();
        AffectedTestPlan.Validate(plan);
        scratch.Save(plan);
        var cache = new AffectedTestCache(scratch.Root, TextWriter.Null);
        Assert.NotNull(cache.Seed);
        var changed = plan.Actions[0] with { Inputs = [new("shared", "changed")] };
        changed = changed with { Identity = AffectedTestPlan.Identity(changed) };
        var selection = cache.Select(changed, plan.Projects[0]);
        Assert.Null(selection.Success);
        Assert.StartsWith("unusable-success:", selection.Reason, StringComparison.Ordinal);
    }

    [Fact]
    public void MalformedSeedRunsFreshNativeTestsAndPreservesTheirFailure()
    {
        using var fixture = new AffectedExecutionFixture();
        fixture.Write("tools/tests/StrataLint.First/Tests.cs", "namespace First; public class Tests { [Xunit.Fact] public void Runs() { Xunit.Assert.Equal(8, Shared.Value()); } }\n");
        var build = fixture.Build();
        new AffectedTestCache(fixture.Root, fixture.Output).Save(DuplicateInputs(fixture.Plan(), actionInputs: false), []);
        var result = fixture.Tests(build, expectedExit: 1);
        Assert.All(result.Projects, project => Assert.True(project.Executed > 0 || project.Error is not null));
        Assert.NotNull(result.Projects.Single(project => project.Project == AffectedExecutionFixture.First).Error);
        Assert.Equal(1, result.Projects.Single(project => project.Project == AffectedExecutionFixture.Second).Executed);
        Assert.Contains("unusable-seed:", fixture.Output.ToString(), StringComparison.Ordinal);
        Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateTests(fixture.Root));
    }

    private static TestInputManifest Manifest()
    {
        var project = new TestProjectInputs("project", [new("shared", "original")], [], [], "");
        project = project with { Identity = AffectedTestPlan.ProjectIdentity(project) };
        var action = new TestAction("project", "Tests", "Tests.Class", ["Tests.Class.Runs"],
            [new("shared", "original")], [], [], project.Identity, "producer", "environment", "");
        action = action with { Identity = AffectedTestPlan.Identity(action) };
        return new(2, new string('a', 64), [project], [action]);
    }

    private static TestInputManifest DuplicateInputs(TestInputManifest plan, bool actionInputs)
    {
        var project = plan.Projects[0];
        if (!actionInputs)
        {
            project = project with { Inputs = [.. project.Inputs, project.Inputs[0]] };
            project = project with { Identity = AffectedTestPlan.ProjectIdentity(project) };
        }
        var actions = plan.Actions.Select(action =>
        {
            if (action.Project != project.Project) return action;
            var changed = action with { ProjectIdentity = project.Identity,
                Inputs = actionInputs ? [.. action.Inputs, action.Inputs[0]] : action.Inputs };
            return changed with { Identity = AffectedTestPlan.Identity(changed) };
        }).ToArray();
        return plan with { Projects = [project, .. plan.Projects.Skip(1)], Actions = actions };
    }

    private sealed class SeedFixture : IDisposable
    {
        internal string Root { get; } = TemporaryFileSystem.Directory.CreateTempSubdirectory("affected-seed-").FullName;
        internal SeedFixture() => TemporaryFileSystem.File.WriteAllText(Path.Combine(Root, "lake-manifest.json"),
            "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"1111111111111111111111111111111111111111\"}]}\n");
        internal void Save(TestInputManifest plan) => new AffectedTestCache(Root, TextWriter.Null).Save(plan, []);
        public void Dispose() => TemporaryFileSystem.Directory.Delete(Root, recursive: true);
    }
}
