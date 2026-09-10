using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class AffectedNativeBoundaryTests
{
    [Fact]
    public void WarmCompilerMetadataRecoversMissingReceiptWithoutEmission()
    {
        var root = TemporaryFileSystem.Directory.CreateTempSubdirectory("warm-compiler-").FullName;
        try
        {
            var import = Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/ci-build-outputs.targets");
            File.WriteAllText(Path.Combine(root, "Warm.csproj"), """
                <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
                <EmitCompilerGeneratedFiles>true</EmitCompilerGeneratedFiles></PropertyGroup>
                <ItemGroup><Compile Remove="Generator/**/*.cs" />
                <ProjectReference Include="Generator/Generator.csproj" OutputItemType="Analyzer" ReferenceOutputAssembly="false" /></ItemGroup></Project>
                """);
            File.WriteAllText(Path.Combine(root, "Value.cs"), "public class Value { public static int Add(int x) => x + 1; }");
            Directory.CreateDirectory(Path.Combine(root, "Generator"));
            File.WriteAllText(Path.Combine(root, "Generator/Generator.csproj"), """
                <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework></PropertyGroup>
                <ItemGroup><Reference Include="Microsoft.CodeAnalysis" HintPath="$(MSBuildToolsPath)/Roslyn/bincore/Microsoft.CodeAnalysis.dll" /></ItemGroup></Project>
                """);
            var marker = Path.Combine(root, "generator-runs.txt");
            File.WriteAllText(Path.Combine(root, "Generator/Generate.cs"), """
                using Microsoft.CodeAnalysis;
                [Generator] public sealed class Generate : ISourceGenerator {
                    public void Initialize(GeneratorInitializationContext context) { }
                    public void Execute(GeneratorExecutionContext context) {
                """ + "System.IO.File.AppendAllText(" + System.Text.Json.JsonSerializer.Serialize(marker) + ", \"ran\\n\");"
                + "context.AddSource(\"GeneratedValue.g.cs\", \"public class GeneratedValue { }\"); } }");
            Run("initial", "build", "Warm.csproj", "-c:Release");
            var assembly = Path.Combine(root, "bin/Release/net10.0/Warm.dll");
            var original = File.ReadAllBytes(assembly);
            Assert.Equal("ran\n", File.ReadAllText(marker));
            var receipt = Path.Combine(root, "obj/Release/net10.0/ci-compiler-arguments.txt");
            Assert.False(File.Exists(receipt));
            var canonicalRoot = Run("project-root", "msbuild", "Warm.csproj", "-nologo", "-getProperty:MSBuildProjectDirectory").Trim();
            string[] capture = ["-p:CustomAfterMicrosoftCommonTargets=" + import,
                "-p:CiRepositoryRoot=" + canonicalRoot, "-p:ProvideCommandLineArgs=true"];
            // The bootstrap imports the same target without a build output inventory.
            var warm = Run("warm-bootstrap", ["build", "Warm.csproj", "-c:Release", "--no-restore", "-v:diag", .. capture]);
            Assert.True(File.Exists(receipt), "Warm Build did not recover the missing compiler argument receipt");
            Assert.NotEmpty(File.ReadAllLines(receipt));
            AssertMetadataOnly(warm, 2);
            Assert.Equal(original, File.ReadAllBytes(assembly));
            Assert.Equal("ran\n", File.ReadAllText(marker));
            File.Delete(receipt);
            var changed = Run("changed-option", ["msbuild", "Warm.csproj", "-p:Configuration=Release", "-v:diag",
                "-t:CaptureCiCompilerMetadata", "-p:CheckForOverflowUnderflow=true",
                "-p:CiBuildOutputRoot=" + Path.Combine(root, "build/ci/build-outputs"), .. capture]);
            Assert.Contains("/checked+", File.ReadAllLines(receipt));
            AssertMetadataOnly(changed, 1);
            Assert.Equal(original, File.ReadAllBytes(assembly));
            Assert.Equal("ran\n", File.ReadAllText(marker));
            var native = File.ReadAllLines(Path.Combine(root, "build/ci/build-outputs/Warm.csproj.native"));
            Assert.Contains("generated_provenance=not-rerun", native);
            Assert.Contains(native, line => line.StartsWith("generated=", StringComparison.Ordinal) && line.EndsWith("GeneratedValue.g.cs", StringComparison.Ordinal));

            string Run(string name, params string[] arguments)
            {
                var result = SharedBuildContractTests.Process(root, "dotnet", arguments,
                    new Dictionary<string, string> { ["DOTNET_CLI_UI_LANGUAGE"] = "en-US" });
                if (Environment.GetEnvironmentVariable("AFFECTED_EVIDENCE_ROOT") is { Length: > 0 } evidence)
                {
                    Directory.CreateDirectory(evidence);
                    File.WriteAllText(Path.Combine(evidence, "compiler-" + name + ".log"), result.Text);
                }
                Assert.True(result.Exit == 0, result.Text);
                return result.Text;
            }
        }
        finally { TemporaryFileSystem.Directory.Delete(root, recursive: true); }

        static void AssertMetadataOnly(string log, int count)
        {
            var tasks = System.Text.RegularExpressions.Regex.Matches(log,
                "Task \\\"Csc\\\".*?Done executing task \\\"Csc\\\"", System.Text.RegularExpressions.RegexOptions.Singleline);
            Assert.Equal(count, tasks.Count);
            Assert.All(tasks, task => Assert.Contains("SkipCompilerExecution=True", task.Value, StringComparison.OrdinalIgnoreCase));
        }
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void SharedSdkSourceInExcludedProjectPreservesSelectedClassesAndDependencies(bool referenced, bool buildOnly)
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
            if (buildOnly)
            {
                var document = System.Xml.Linq.XDocument.Load(Path.Combine(fixture.Root, AffectedExecutionFixture.First));
                document.Descendants("ProjectReference").Single(element => element.Attribute("Include")!.Value.Contains("StrataLint.ScriptTests", StringComparison.Ordinal))
                    .SetAttributeValue("ReferenceOutputAssembly", "false");
                fixture.Write(AffectedExecutionFixture.First, document.ToString());
            }
            else fixture.Write("tools/tests/StrataLint.First/Tests.cs", "namespace First; public class Tests { [Xunit.Fact] public void Runs() { Xunit.Assert.Equal(7, ExcludedDependency.Value()); } }\n");
        }
        fixture.Run("dotnet", "restore", "tools/StrataLint.sln", "--use-lock-file");
        var build = fixture.Build();
        var native = CommonExecutionEvidence.Read<NativeProject[]>(fixture.Root, AffectedTestPlan.NativePath);
        Assert.DoesNotContain("tools/StrataLint.Shared/Value.cs", native.Single(project => project.Project == AffectedExecutionFixture.First).Inputs);
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
        if (referenced && !buildOnly)
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

    [Theory]
    [InlineData("input_ids", "inputs", false)]
    [InlineData("edge_ids", "edges", false)]
    [InlineData("unknown_ids", "unknown", false)]
    [InlineData("input_ids", "inputs", true)]
    [InlineData("edge_ids", "edges", true)]
    [InlineData("unknown_ids", "unknown", true)]
    public void CorruptSharedReferencesCannotSupplyASeed(string references, string table, bool duplicate)
    {
        using var scratch = new SeedFixture();
        scratch.Save(Manifest());
        CorruptSharedSeed(scratch.Root, references, table, duplicate);
        var cache = new AffectedTestCache(scratch.Root, TextWriter.Null);
        Assert.Null(cache.Seed);
        Assert.StartsWith("unusable-seed:", cache.Select(Manifest().Actions[0]).Reason, StringComparison.Ordinal);
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

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MalformedSeedRunsFreshNativeTestsAndPreservesTheirFailure(bool dangling)
    {
        using var fixture = new AffectedExecutionFixture();
        fixture.Write("tools/tests/StrataLint.First/Tests.cs", "namespace First; public class Tests { [Xunit.Fact] public void Runs() { Xunit.Assert.Equal(8, Shared.Value()); } }\n");
        var build = fixture.Build();
        new AffectedTestCache(fixture.Root, fixture.Output).Save(dangling ? fixture.Plan() : DuplicateInputs(fixture.Plan(), actionInputs: false), []);
        if (dangling) CorruptSharedSeed(fixture.Root, "input_ids", "inputs", duplicate: false);
        var result = fixture.Tests(build, expectedExit: 1);
        Assert.All(result.Projects, project => Assert.True(project.Executed > 0 || project.Error is not null));
        Assert.NotNull(result.Projects.Single(project => project.Project == AffectedExecutionFixture.First).Error);
        Assert.Equal(1, result.Projects.Single(project => project.Project == AffectedExecutionFixture.Second).Executed);
        Assert.Contains("unusable-seed:", fixture.Output.ToString(), StringComparison.Ordinal);
        Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateTests(fixture.Root));
    }

    private static TestInputManifest Manifest()
    {
        var project = new TestProjectInputs("project", [new("shared", "original")], ["project -> dependency"], ["unknown-input"], "");
        project = project with { Identity = AffectedTestPlan.ProjectIdentity(project) };
        var action = new TestAction("project", "Tests", "Tests.Class", ["Tests.Class.Runs"],
            [new("shared", "original")], [], [], project.Identity, "producer", "environment", "");
        action = action with { Identity = AffectedTestPlan.Identity(action) };
        return new(3, new string('a', 64), [project], [action]);
    }

    private static void CorruptSharedSeed(string root, string references, string table, bool duplicate)
    {
        var path = Directory.GetFiles(Path.Combine(root, AffectedTestCache.CachePath), "seed.json", SearchOption.AllDirectories).Single();
        var seed = System.Text.Json.Nodes.JsonNode.Parse(File.ReadAllText(path))!;
        var manifest = seed["manifest"]!;
        var values = manifest[table]!.AsArray();
        if (duplicate) values.Add(values[0]!.DeepClone());
        else manifest["projects"]![0]![references] = new System.Text.Json.Nodes.JsonArray(values.Count);
        File.WriteAllText(path, seed.ToJsonString());
        File.WriteAllText(path + ".sha256", CommonExecutionEvidence.Hash(path));
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
