using System.Text;

namespace StrataLint.ArchitectureTests;

public sealed partial class EngineeringPathFilterTests
{
    private const string DigestionOpenPath = "Meta/Digestion/backfill/source/residual-open/atom.yaml";
    private const string DigestionClosedPath = "Meta/Digestion/backfill/source/absorbed-closed/atom.yaml";
    private const string DigestionCasPath =
        "Meta/Digestion/atoms/sha256/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    private const string DigestionFileMap = """
        [[files]]
        pattern = "Meta/Digestion/backfill/**"
        admission_plane = "content"
        [[files]]
        pattern = "Meta/Digestion/atoms/sha256/*"
        admission_plane = "content"
        [[files]]
        pattern = "Meta/Digestion/atomizers.toml"
        admission_plane = "judge"
        [[files]]
        pattern = "notes/**"
        admission_plane = "content"
        """;

    [Theory]
    [InlineData(DigestionOpenPath)]
    [InlineData(DigestionCasPath)]
    [InlineData("Meta/Digestion/backfill/source/source.toml")]
    public void DigestionDataWithoutEngineeringDependentsSelectsNoTests(string path)
    {
        var plan = EvaluateDigestion([path], Topology(scribeTestsReferenceScribe: true));

        Assert.Equal(EngineeringTestPlanKind.None, plan.Kind);
        Assert.Empty(plan.Projects);
        Assert.Equal(path, Assert.Single(plan.ChangedPaths));
    }

    [Fact]
    public void DigestionStatusMoveSelectsNoEngineeringTests()
    {
        var plan = EvaluateDigestion([DigestionOpenPath, DigestionClosedPath],
            Topology(scribeTestsReferenceScribe: true));

        Assert.Equal(EngineeringTestPlanKind.None, plan.Kind);
        Assert.Empty(plan.Projects);
        Assert.Equal(2, plan.ChangedPaths.Length);
    }

    [Theory]
    [InlineData("Meta/Digestion/atomizers.toml")]
    [InlineData("notes/unknown.txt")]
    [InlineData("Meta/Digestion/backfill/source/unknown/atom.yaml")]
    [InlineData("Meta/Digestion/atoms/sha256/not-a-hash")]
    public void NonDataAndUnknownDigestionPathsKeepEngineeringFallback(string path)
    {
        var plan = EvaluateDigestion([path], Topology(scribeTestsReferenceScribe: true));

        Assert.Equal(EngineeringTestPlanKind.Full, plan.Kind);
        Assert.Contains(EngineTestsProject, plan.Projects);
    }

    [Theory]
    [InlineData("judge")]
    [InlineData("invalid")]
    public void DigestionExemptionRequiresContentOnlyAdmissionClassification(string plane)
    {
        var plan = EvaluateDigestion([DigestionOpenPath], Topology(scribeTestsReferenceScribe: true),
            fileMap: DigestionFileMap.Replace("\"content\"", $"\"{plane}\"", StringComparison.Ordinal));

        Assert.Equal(EngineeringTestPlanKind.Full, plan.Kind);
        Assert.NotEmpty(plan.Projects);
    }

    [Fact]
    public void MissingAdmissionDecisionDoesNotExemptDigestionData()
    {
        var snapshot = Topology(scribeTestsReferenceScribe: true);

        var plan = EngineeringTestPlanPolicy.EvaluateOrdinary([DigestionOpenPath], snapshot, snapshot);

        Assert.Equal(EngineeringTestPlanKind.Full, plan.Kind);
        Assert.NotEmpty(plan.Projects);
    }

    [Fact]
    public void MixedDigestionAndUnknownDeltaKeepsEngineeringFallback()
    {
        var plan = EvaluateDigestion([DigestionOpenPath, "notes/unknown.txt"],
            Topology(scribeTestsReferenceScribe: true));

        Assert.Equal(EngineeringTestPlanKind.Full, plan.Kind);
        Assert.NotEmpty(plan.Projects);
    }

    [Fact]
    public void FullOverrideStillTestsDigestionData()
    {
        var plan = EvaluateDigestion([DigestionOpenPath], Topology(scribeTestsReferenceScribe: true), full: true);

        Assert.Equal(EngineeringTestPlanKind.Full, plan.Kind);
        Assert.Contains(EngineTestsProject, plan.Projects);
        Assert.DoesNotContain(ScriptTestsProject, plan.Projects);
    }

    [Fact]
    public void DigestionCompileInputRetainsItsProjectAndReverseDependents()
    {
        var snapshot = new TestProjectTopologySnapshot(Topology(scribeTestsReferenceScribe: true).Projects
            .Select(project => project.Path == ScribeProject
                ? ProjectWithCompile(ScribeProject, isTest: false, "../../Meta/Digestion/backfill/**/*.yaml")
                : project).ToArray());

        var plan = EvaluateDigestion([DigestionOpenPath], snapshot);

        Assert.Equal(EngineeringTestPlanKind.Selected, plan.Kind);
        Assert.Equal([ArchitectureTestsProject, ScribeTestsProject], plan.Projects.ToArray());
    }

    [Fact]
    public void DigestionOwnershipDoesNotReenableExcludedScriptTests()
    {
        var snapshot = new TestProjectTopologySnapshot(Topology(scribeTestsReferenceScribe: true).Projects
            .Select(project => project.Path == ScriptTestsProject
                ? ProjectWithCompile(ScriptTestsProject, isTest: true, "../../../Meta/Digestion/backfill/**/*.yaml")
                : project).ToArray());

        var plan = EvaluateDigestion([DigestionOpenPath], snapshot);

        Assert.Equal(EngineeringTestPlanKind.None, plan.Kind);
        Assert.Empty(plan.Projects);
    }

    private static EngineeringTestPlan EvaluateDigestion(IReadOnlyList<string> paths,
        TestProjectTopologySnapshot snapshot, bool full = false, string fileMap = DigestionFileMap) =>
        EngineeringTestPlanPolicy.EvaluateOrdinary(paths, snapshot, snapshot, full,
            AdmissionPlanePolicy.Evaluate(Encoding.UTF8.GetBytes(fileMap), paths));
}
