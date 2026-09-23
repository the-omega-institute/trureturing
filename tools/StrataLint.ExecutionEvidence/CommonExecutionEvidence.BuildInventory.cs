namespace StrataLint.EngineeringScope;

internal sealed record BuiltTestProject(string Project, string Assembly);

internal static partial class CommonExecutionEvidence
{
    internal const string BuildTestsPath = RootPath + "/build-outputs/test-assemblies.json";

    internal static Dictionary<string, string> TestAssemblies(string root, CommonStageRecord build)
    {
        if (!build.Materials.Any(material => material.Path == BuildTestsPath))
            throw new InvalidDataException("build has no test runtime inventory");
        var tests = CommonExecutionEvidence.Read<BuiltTestProject[]>(root, BuildTestsPath);
        foreach (var test in tests)
            if (!build.Materials.Any(material => material.Path == test.Assembly))
                throw new InvalidDataException("unbound test runtime: " + test.Project);
        return tests.ToDictionary(test => test.Project, test => test.Assembly, StringComparer.Ordinal);
    }
}
