using System.Runtime.InteropServices;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed partial class ProductionCliEnvironment
{
    private ScribeTestMapStore? TryCreateTestMapStore(
        string root,
        out string? disabledOutcome)
    {
        disabledOutcome = null;
        try
        {
            var output = BoundedProcessRunner.Run(
                "dotnet",
                ["--version"],
                repositoryRoot,
                BoundedProcessRunner.HangDetectionBudget,
                maximumOutputBytes: 4096);
            if (output.ExitCode != 0)
            {
                disabledOutcome = "disabled:dotnet-version-exit-" + output.ExitCode;
                return null;
            }

            var version = new UTF8Encoding(false, true).GetString(output.StandardOutput).Trim();
            if (version.Length == 0)
            {
                disabledOutcome = "disabled:dotnet-version-empty";
                return null;
            }

            var environment = new ScribeTestMapEnvironment(
                RuntimeInformation.RuntimeIdentifier,
                RuntimeInformation.FrameworkDescription,
                version);
            return new ScribeTestMapStore(
                new DirectoryScribeTestMapStorage(root),
                environment);
        }
        catch (Exception exception)
        {
            disabledOutcome = "disabled:dotnet-version-" + exception.GetType().Name;
            return null;
        }
    }

    private static void WriteTestMapCacheEvent(string inputDigest, string outcome)
    {
        try
        {
            Console.Error.WriteLine(JsonSerializer.Serialize(new
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
