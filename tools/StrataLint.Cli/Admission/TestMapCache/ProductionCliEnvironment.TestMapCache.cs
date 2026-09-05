using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed partial class ProductionCliEnvironment
{
    internal Func<ScribeTestMapEnvironment> DescribeTestMapEnvironment { get; init; } =
        MsBuildCompileOracle.DescribeEnvironment;

    internal TextWriter? TestMapCacheError { get; init; }

    private ScribeTestMapStore? TryCreateTestMapStore(
        string root,
        out string? disabledOutcome)
    {
        disabledOutcome = null;
        try
        {
            return new ScribeTestMapStore(
                new DirectoryScribeTestMapStorage(root),
                DescribeTestMapEnvironment());
        }
        catch (Exception exception)
        {
            disabledOutcome = "disabled:dotnet-version-" + exception.GetType().Name;
            return null;
        }
    }

    private void WriteTestMapCacheEvent(string inputDigest, string outcome)
    {
        try
        {
            (TestMapCacheError ?? Console.Error).WriteLine(JsonSerializer.Serialize(new
            {
                @event = "test_map_cache",
                scope = "admission-check",
                input_digest = inputDigest,
                outcome,
            }));
        }
        catch
        {
            // Cache observability cannot change the admission decision.
        }
    }
}
