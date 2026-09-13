using System.Text.Json;

namespace StrataLint.ArchitectureTests;

public sealed partial class EngineeringPathFilterTests
{
    private const string ScribeProject = "tools/StrataLint.Scribe/StrataLint.Scribe.csproj";
    private const string EngineProject = "tools/StrataLint.Engine/StrataLint.Engine.csproj";
    private const string ScribeTestsProject = "tools/tests/StrataLint.Scribe.Tests/StrataLint.Scribe.Tests.csproj";
    private const string EngineTestsProject = "tools/tests/StrataLint.Engine.Tests/StrataLint.Engine.Tests.csproj";
    private const string ArchitectureTestsProject = "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj";
    private const string ScriptTestsProject = "tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj";
    private const string TestSupportProject = "tools/TestSupport/StrataLint.TestSupport/StrataLint.TestSupport.csproj";

    [Fact]
    public void ScribeChangeSelectsBaseReverseTestProjectClosure()
    {
        var plan = EngineeringTestPlanPolicy.EvaluateOrdinary(["tools/StrataLint.Scribe/DocumentEmitter.cs"], Manifest());
        Assert.Equal(EngineeringTestPlanKind.Selected, plan.Kind);
        Assert.Equal([ArchitectureTestsProject, ScribeTestsProject], plan.Projects.ToArray());
    }

    [Fact]
    public void TestProjectChangeSelectsItselfAndItsBaseReverseDependents()
    {
        var plan = EngineeringTestPlanPolicy.EvaluateOrdinary(["tools/tests/StrataLint.Engine.Tests/EngineTests.cs"], Manifest());
        Assert.Equal([ArchitectureTestsProject, EngineTestsProject], plan.Projects.ToArray());
    }

    [Fact]
    public void FullPlanExcludesXunitReferencingProjectThatDeclaresItselfNonTest()
    {
        var plan = EngineeringTestPlanPolicy.EvaluateOrdinary(["tools/StrataLint.Engine/Code.cs"], Manifest(), full: true);
        Assert.DoesNotContain(TestSupportProject, plan.Projects);
        Assert.DoesNotContain(ScriptTestsProject, plan.Projects);
        Assert.Equal([ArchitectureTestsProject, EngineTestsProject, ScribeTestsProject], plan.Projects.ToArray());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MissingOwnerFailsInsteadOfSelectingFullSuite(bool full)
    {
        var error = Assert.Throws<InvalidDataException>(() =>
            EngineeringTestPlanPolicy.EvaluateOrdinary(["tools/Unregistered/Code.cs"], Manifest(), full));
        Assert.Contains("tools/Unregistered/Code.cs", error.Message, StringComparison.Ordinal);
        Assert.Contains("missing input registration", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ConflictingInputDeclarationsFail()
    {
        var error = Assert.Throws<InvalidDataException>(() =>
            EngineeringTestPlanPolicy.EvaluateOrdinary(["tools/StrataLint.Engine/Code.cs"], Manifest(conflicting: true)));
        Assert.Contains("conflicting input registrations", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void MissingImpactTargetFailsWithItsIdentity()
    {
        var error = Assert.Throws<InvalidDataException>(() => Manifest(missingReference: true));
        Assert.Contains("missing.csproj", error.Message, StringComparison.Ordinal);
        Assert.Contains("missing impact project registration", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ConflictingProjectRegistrationFails()
    {
        var error = Assert.Throws<InvalidDataException>(() => Manifest(duplicate: true));
        Assert.Contains(EngineProject, error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ScriptTestsAreExcludedEvenWhenTheirDeclaredInputsChange()
    {
        var plan = EngineeringTestPlanPolicy.EvaluateOrdinary(["tools/tests/StrataLint.ScriptTests/Probe.cs"], Manifest());
        Assert.Empty(plan.Projects);
        Assert.Contains("not-required", plan.Reason, StringComparison.Ordinal);
    }

    [Fact]
    public void SelectedProjectFailureDoesNotRetryTheWholeSolution()
    {
        var plan = EngineeringTestPlanPolicy.EvaluateOrdinary(["tools/StrataLint.Scribe/DocumentEmitter.cs"], Manifest());
        Assert.Equal(EngineeringTestPlanKind.Selected, plan.Kind);
        var calls = new System.Collections.Concurrent.ConcurrentBag<string>();
        var exit = EngineeringTestExecutor.Execute(plan, project =>
        {
            calls.Add(project.ProjectPath);
            return project.ProjectPath == ArchitectureTestsProject ? 17 : 23;
        });
        Assert.Equal(17, exit);
        Assert.Equal([ArchitectureTestsProject, ScribeTestsProject], calls.Order(StringComparer.Ordinal).ToArray());
    }

    [Fact]
    public void PreManifestComparisonRequiresExplicitProjectRegistration()
    {
        var error = Assert.Throws<InvalidDataException>(() => Manifest().ReadComparison(ComparisonSnapshot("old project")));
        Assert.Contains(EngineProject, error.Message, StringComparison.Ordinal);
        Assert.Contains("missing pre-manifest comparison project registration", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DeclaredPreManifestComparisonChecksExactProjectBytes()
    {
        const string content = "opaque registered project bytes";
        var project = Project(EngineProject, "production") with
        {
            sha256 = Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(System.Text.Encoding.UTF8.GetBytes(content))),
        };
        var manifest = EngineeringInputManifest.Parse(JsonSerializer.Serialize(new
        {
            schema_version = 1, projects = new[] { project }, inputs = Array.Empty<object>(),
            comparison_projects = new[] { EngineProject },
        }), "fixture");
        var snapshot = ComparisonSnapshot(content);
        var declared = manifest.ReadComparison(snapshot);
        Assert.Equal(EngineProject, Assert.Single(RepositoryRules.ReadDeclaredProjects(snapshot, declared).Projects).Path);
        var error = Assert.Throws<InvalidDataException>(() =>
            RepositoryRules.ReadDeclaredProjects(ComparisonSnapshot(content + " changed"), declared));
        Assert.Contains(EngineProject, error.Message, StringComparison.Ordinal);
        Assert.Contains("sha256 differs", error.Message, StringComparison.Ordinal);
    }

    private static RepositorySnapshot ComparisonSnapshot(string content) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create(
        [
            RawRepositoryEntry.FromText("Meta/FILEMAP.toml", "[[files]]\npattern = \"tools/**\"\nadmission_plane = \"judge\"\n"),
            RawRepositoryEntry.FromText(EngineProject, content),
        ]))).Snapshot;

    private static EngineeringInputManifest Manifest(bool conflicting = false, bool missingReference = false, bool duplicate = false,
        string? digestionOwner = null)
    {
        var projects = new[]
        {
            Project(EngineProject, "production"), Project(ScribeProject, "production"), Project(TestSupportProject, "support"),
            Project(EngineTestsProject, "test", EngineProject), Project(ScribeTestsProject, "test", ScribeProject),
            Project(ArchitectureTestsProject, "harness", EngineTestsProject, ScribeProject),
            Project(ScriptTestsProject, "harness", missingReference ? "missing.csproj" : EngineProject),
        }.ToList();
        if (duplicate) projects.Add(Project(EngineProject, "production"));
        var inputs = projects.Select(project => new
        {
            patterns = new[] { project.inputs[0] }, projects = new[] { project.path },
        }).ToList();
        inputs.Add(new { patterns = new[] { "Meta/Digestion/backfill/**", "Meta/Digestion/atoms/sha256/*" },
            projects = digestionOwner is null ? Array.Empty<string>() : new[] { digestionOwner } });
        if (conflicting) inputs.Add(new { patterns = new[] { "tools/StrataLint.Engine/**" }, projects = new[] { EngineProject } });
        return EngineeringInputManifest.Parse(JsonSerializer.Serialize(new { schema_version = 1, projects, inputs }), "fixture");
    }

    private sealed record ProjectDeclaration(string path, string assembly, string role, string[] references, string[] inputs, string sha256);
    private static ProjectDeclaration Project(string path, string role, params string[] references) =>
        new(path, Path.GetFileNameWithoutExtension(path), role, references, [Path.GetDirectoryName(path)!.Replace('\\', '/') + "/**"], new string('a', 64));
}
