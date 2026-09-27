namespace StrataLint.TestSupport;

// Synthetic repositories own their event inputs. Use the scope only in a
// serialized test collection; child processes can use LocalAssignments.
public sealed class CiFixtureEnvironment : IDisposable
{
    private static readonly string[] Variables =
    [
        "GITHUB_EVENT_NAME", "GITHUB_EVENT_PATH", "CANDIDATE_SHA",
        "CI_WORKFLOW_INPUTS", "CI_PUSH_BEFORE", "CI_PUSH_AFTER",
    ];
    private readonly Dictionary<string, string?> previous =
        Variables.ToDictionary(name => name, Environment.GetEnvironmentVariable);

    public static IEnumerable<string> LocalAssignments => Variables.Select(name => name + "=");

    public CiFixtureEnvironment()
    {
        foreach (var name in Variables) Environment.SetEnvironmentVariable(name, null);
    }

    public void Dispose()
    {
        foreach (var (name, value) in previous) Environment.SetEnvironmentVariable(name, value);
    }
}
