using System.Collections.Immutable;
using System.Text.Json;

namespace Trureturing.Truth;

/// <summary>
/// Successful CI evidence for one dev source commit. This does not assert that the producer's
/// report artifact is present or valid, nor that the source is on protected dev.
/// </summary>
public sealed record TruthReleasePushRun(
    string SourceCommit,
    long WorkflowId,
    long RunId,
    int RunAttempt,
    ImmutableArray<TruthReleaseRequiredCheck> RequiredChecks);

public static class TruthReleasePushRunSelector
{
    public const string WorkflowPath = ".github/workflows/ci-push.yml";

    /// <summary>
    /// Selects the newest successful dev push run for an exact source commit. The caller supplies
    /// the GitHub workflow response resolved by filename, workflow_runs rows (all supplied pages),
    /// and a reader for jobs of the requested run ID and attempt, including all pages. API failures
    /// propagate; malformed evidence throws FormatException; no qualifying run returns null.
    /// The caller owns protected-dev history selection and must separately obtain and validate the
    /// selected run's producer artifact. Missing artifacts must not trigger report reproduction.
    /// </summary>
    public static TruthReleasePushRun? Select(
        string sourceCommit,
        JsonElement workflow,
        IEnumerable<JsonElement> runs,
        Func<long, int, IEnumerable<JsonElement>> readJobs)
    {
        TruthExportValidation.RequireGitObjectId(sourceCommit, nameof(sourceCommit));
        ArgumentNullException.ThrowIfNull(runs);
        ArgumentNullException.ThrowIfNull(readJobs);
        if (Text(workflow, "path") != WorkflowPath)
        {
            throw new FormatException("truth release workflow does not resolve to " + WorkflowPath);
        }

        var workflowId = PositiveNumber(workflow, "id");
        foreach (var run in runs.OrderByDescending(item => PositiveNumber(item, "id")))
        {
            if (PositiveNumber(run, "workflow_id") != workflowId
                || Text(run, "path") != WorkflowPath
                || Text(run, "event") != "push"
                || Text(run, "head_branch") != "dev"
                || Text(run, "head_sha") != sourceCommit
                || !Successful(run))
            {
                continue;
            }

            var runId = PositiveNumber(run, "id");
            var attemptValue = PositiveNumber(run, "run_attempt");
            if (attemptValue > int.MaxValue)
            {
                throw new FormatException("GitHub run_attempt exceeds the supported integer range.");
            }

            var attempt = (int)attemptValue;
            var jobs = readJobs(runId, attempt).ToArray();
            var checks = ImmutableArray.CreateBuilder<TruthReleaseRequiredCheck>();
            foreach (var name in TruthReleaseManifestReader.RequiredCheckNames)
            {
                var matching = jobs.Where(job => Text(job, "name") == name).ToArray();
                if (matching.Length != 1)
                {
                    break;
                }

                var job = matching[0];
                if (PositiveNumber(job, "run_id") != runId
                    || PositiveNumber(job, "run_attempt") != attempt
                    || Text(job, "head_sha") != sourceCommit
                    || !Successful(job))
                {
                    break;
                }

                checks.Add(new TruthReleaseRequiredCheck(name, "success"));
            }

            if (checks.Count == TruthReleaseManifestReader.RequiredCheckNames.Length)
            {
                return new TruthReleasePushRun(sourceCommit, workflowId, runId, attempt, checks.ToImmutable());
            }
        }

        return null;
    }

    private static bool Successful(JsonElement value) =>
        Text(value, "status") == "completed" && Text(value, "conclusion") == "success";

    private static string Text(JsonElement value, string key)
    {
        var field = Field(value, key);
        return field.ValueKind == JsonValueKind.String
            ? field.GetString()!
            : throw new FormatException($"GitHub evidence field '{key}' must be a string.");
    }

    private static long PositiveNumber(JsonElement value, string key)
    {
        var field = Field(value, key);
        return field.ValueKind == JsonValueKind.Number && field.TryGetInt64(out var number) && number > 0
            ? number
            : throw new FormatException($"GitHub evidence field '{key}' must be a positive integer.");
    }

    private static JsonElement Field(JsonElement value, string key) =>
        value.ValueKind == JsonValueKind.Object && value.TryGetProperty(key, out var field)
            ? field
            : throw new FormatException($"GitHub evidence is missing '{key}'.");
}
