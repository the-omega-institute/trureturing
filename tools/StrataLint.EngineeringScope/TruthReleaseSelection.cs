using System.Globalization;
using System.Text.Json;
using Trureturing.Truth;

namespace StrataLint.EngineeringScope;

internal static class TruthReleaseSelection
{
    // API collection belongs to the workflow helper; the named-run predicate and
    // transport owner remain the authorities for checks and artifact identity.
    internal static int Run(IReadOnlyList<string> arguments, TextWriter output)
    {
        if (arguments.Count != 3 || arguments[1] != "--input")
            throw new ArgumentException("truth-release-select --input FILE");
        using var document = JsonDocument.Parse(File.ReadAllBytes(arguments[2]));
        var input = document.RootElement;
        var commit = input.GetProperty("source_commit").GetString()!;
        var runs = input.GetProperty("runs").EnumerateArray().ToList();
        while (TruthReleasePushRunSelector.Select(commit, input.GetProperty("workflow"), runs,
                   (id, attempt) => input.GetProperty("jobs").GetProperty($"{id}/{attempt}").EnumerateArray()) is { } selected)
        {
            var name = CiTransport.ArtifactName("current", selected.RunId, selected.RunAttempt);
            var artifacts = input.GetProperty("artifacts").GetProperty(selected.RunId.ToString(CultureInfo.InvariantCulture))
                .EnumerateArray().Where(artifact => Matches(artifact, name, selected)).ToArray();
            if (artifacts.Length == 1)
            {
                output.WriteLine(JsonSerializer.Serialize(new
                {
                    publish_ready = true, source_commit = commit, run_id = selected.RunId, run_attempt = selected.RunAttempt,
                    artifact_id = artifacts[0].GetProperty("id").GetInt64(), artifact_name = name,
                    required_checks = selected.RequiredChecks.Select(check => new { name = check.Name, conclusion = check.Conclusion }),
                }));
                return 0;
            }
            runs.RemoveAll(run => run.GetProperty("id").GetInt64() == selected.RunId);
        }
        output.WriteLine("{\"publish_ready\":false}");
        return 0;
    }

    private static bool Matches(JsonElement artifact, string name, TruthReleasePushRun selected) =>
        artifact.ValueKind == JsonValueKind.Object
        && artifact.TryGetProperty("id", out var id) && id.ValueKind == JsonValueKind.Number && id.TryGetInt64(out var number) && number > 0
        && artifact.TryGetProperty("name", out var artifactName) && artifactName.ValueKind == JsonValueKind.String && artifactName.GetString() == name
        && artifact.TryGetProperty("expired", out var expired) && expired.ValueKind == JsonValueKind.False
        && artifact.TryGetProperty("workflow_run", out var run) && run.ValueKind == JsonValueKind.Object
        && run.TryGetProperty("id", out var runId) && runId.ValueKind == JsonValueKind.Number && runId.TryGetInt64(out var runNumber) && runNumber == selected.RunId
        && run.TryGetProperty("head_sha", out var head) && head.ValueKind == JsonValueKind.String && head.GetString() == selected.SourceCommit;
}
