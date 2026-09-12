namespace StrataLint.ArchitectureTests;

public sealed partial class EngineeringPathFilterTests
{
    private const string DigestionOpenPath = "Meta/Digestion/backfill/source/residual-open/atom.yaml";
    private const string DigestionClosedPath = "Meta/Digestion/backfill/source/absorbed-closed/atom.yaml";
    private const string DigestionCasPath = "Meta/Digestion/atoms/sha256/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";

    [Theory]
    [InlineData(DigestionOpenPath)]
    [InlineData(DigestionCasPath)]
    [InlineData("Meta/Digestion/backfill/source/source.toml")]
    public void DigestionDataWithoutEngineeringDependentsSelectsNoTests(string path)
    {
        var plan = EngineeringTestPlanPolicy.EvaluateOrdinary([path], Manifest());
        Assert.Equal(EngineeringTestPlanKind.None, plan.Kind);
        Assert.Empty(plan.Projects);
        Assert.Equal(path, Assert.Single(plan.ChangedPaths));
    }

    [Fact]
    public void DigestionStatusMoveSelectsNoEngineeringTests()
    {
        var plan = EngineeringTestPlanPolicy.EvaluateOrdinary([DigestionOpenPath, DigestionClosedPath], Manifest());
        Assert.Empty(plan.Projects);
        Assert.Equal(2, plan.ChangedPaths.Length);
    }

    [Fact]
    public void FullOverrideStillTestsDigestionData()
    {
        var plan = EngineeringTestPlanPolicy.EvaluateOrdinary([DigestionOpenPath], Manifest(), full: true);
        Assert.Contains(EngineTestsProject, plan.Projects);
        Assert.DoesNotContain(ScriptTestsProject, plan.Projects);
    }

    [Fact]
    public void DigestionCompileInputRetainsItsProjectAndReverseDependents()
    {
        var plan = EngineeringTestPlanPolicy.EvaluateOrdinary([DigestionOpenPath], Manifest(digestionOwner: ScribeProject));
        Assert.Equal([ArchitectureTestsProject, ScribeTestsProject], plan.Projects.ToArray());
    }

    [Fact]
    public void DigestionOwnershipDoesNotReenableExcludedScriptTests()
    {
        var plan = EngineeringTestPlanPolicy.EvaluateOrdinary([DigestionOpenPath], Manifest(digestionOwner: ScriptTestsProject));
        Assert.Empty(plan.Projects);
    }
}
