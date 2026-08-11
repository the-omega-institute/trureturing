namespace StrataLint.Cli;

internal enum TestSelectionEvent
{
    PullRequest,
    DevPush,
}

internal static class TestSelectionPolicy
{
    internal const string ArchitectureTests =
        "Meta/StrataLint/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj";
    internal const string EngineTests =
        "Meta/StrataLint/StrataLint.Tests/StrataLint.Tests.csproj";
    internal const string ScribeTests =
        "Meta/StrataLint/StrataLint.Scribe.Tests/StrataLint.Scribe.Tests.csproj";

    private const string AcceptedEvidencePrefix = "Meta/StrataLint/Golden/Frozen/accepted/";

    internal static IReadOnlyList<string> Select(
        TestSelectionEvent eventKind,
        IReadOnlyList<string> changedPaths)
    {
        ArgumentNullException.ThrowIfNull(changedPaths);
        if (!Enum.IsDefined(eventKind))
        {
            throw new ArgumentOutOfRangeException(nameof(eventKind));
        }

        if (eventKind == TestSelectionEvent.DevPush || !AreCanonical(changedPaths))
        {
            return FullSuite();
        }

        // R-A is deliberately a named code branch. Adding a rule requires
        // editing this policy and extending its architecture proof.
        if (changedPaths.All(IsAcceptedEvidence))
        {
            return [ArchitectureTests];
        }

        return FullSuite();
    }

    internal static ExplicitCommandResult Run(IReadOnlyList<string> arguments)
    {
        if (arguments.Count < 2 || arguments[0] != "--event")
        {
            return new ExplicitCommandResult(
                2,
                "",
                "USAGE: StrataLint select-tests --event pull-request|dev-push <changed-path>...\n");
        }

        var eventKind = arguments[1] switch
        {
            "pull-request" => TestSelectionEvent.PullRequest,
            "dev-push" => TestSelectionEvent.DevPush,
            _ => (TestSelectionEvent?)null,
        };
        if (eventKind is null)
        {
            return new ExplicitCommandResult(2, "", $"UNRECOGNIZED_TEST_EVENT {arguments[1]}\n");
        }

        var selected = Select(eventKind.Value, arguments.Skip(2).ToArray());
        return new ExplicitCommandResult(0, string.Join('\n', selected) + "\n", "");
    }

    private static bool IsAcceptedEvidence(string path) =>
        path.StartsWith(AcceptedEvidencePrefix, StringComparison.Ordinal);

    private static bool AreCanonical(IReadOnlyList<string> paths) =>
        paths.Count > 0
        && paths.All(static path =>
            !string.IsNullOrWhiteSpace(path)
            && !Path.IsPathRooted(path)
            && !path.Contains('\\', StringComparison.Ordinal)
            && !path.StartsWith("./", StringComparison.Ordinal)
            && !path.Split('/').Contains("..", StringComparer.Ordinal));

    private static IReadOnlyList<string> FullSuite() =>
        [ArchitectureTests, EngineTests, ScribeTests];
}
