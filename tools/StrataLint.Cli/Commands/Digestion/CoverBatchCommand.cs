using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Cli;

internal static partial class CoverBatchCommand
{
    internal static CommandResult Run(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        DateTimeOffset recordedAtUtc,
        IReadOnlyList<string> arguments)
    {
        BatchArguments options;
        try
        {
            options = Parse(repositoryRoot, arguments);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new(false, string.Empty, $"COVER_BATCH_INPUT_INVALID {exception.Message}\n", 2);
        }

        using var reportBundle = (leanReportSource as PrecomputedLeanReportSource)?.Capture();
        CoverAtomCommand.Session session;
        BatchPlan plan;
        try
        {
            session = new CoverAtomCommand.Session(repositoryRoot, repository, reportBundle is null ? leanReportSource : reportBundle,
                recordedAtUtc, options.BaseRevision, options.Items[0].Gids[0]);
            plan = Plan(options.Items, session.Document);
        }
        catch (BatchInputException exception)
        {
            return new(false, string.Empty, $"COVER_BATCH_INPUT_INVALID {exception.Message}\n", 2);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            var output = new StringBuilder();
            foreach (var item in options.Items)
                Render(output, item, "blocked", "shared context unavailable: " + exception.Message);
            return new(false, output.ToString(), $"COVER_BATCH_ABORTED {exception.Message}\n", 1);
        }

        var results = new StringBuilder();
        var failures = new Dictionary<string, string>(StringComparer.Ordinal);
        string? aborted = null;
        var successful = true;
        foreach (var atomId in plan.Order)
        {
            var dependencyFailure = plan.Children[atomId].Select(child => failures.GetValueOrDefault(child))
                .FirstOrDefault(reason => reason is not null);
            if (!plan.Items.TryGetValue(atomId, out var item))
            {
                if (dependencyFailure is not null) failures[atomId] = dependencyFailure;
                continue;
            }

            if (aborted is not null || dependencyFailure is not null)
            {
                successful = false;
                var reason = aborted is not null ? "batch aborted: " + aborted : "dependency failed: " + dependencyFailure;
                failures[atomId] = dependencyFailure ?? atomId;
                Render(results, item, "blocked", reason);
                continue;
            }

            var existing = session.Document.RequireDigestionEntries()
                .Where(entry => entry.AtomId == atomId).ToArray();
            var alreadyApplied = existing.Length == 1 && item.Gids.All(existing[0].CoverageGids.Contains);
            var result = session.Apply(atomId, item.Gids);
            var reasonText = result.Error.Trim();
            if (!result.Success)
            {
                successful = false;
                failures[atomId] = atomId;
                if (session.Invalidated) aborted = reasonText;
            }
            Render(results, item, result.Success ? alreadyApplied ? "already_applied" : "applied" : "failed",
                result.Success ? alreadyApplied ? "coverage bindings validated" : "coverage committed" : reasonText);
        }

        if (aborted is not null)
            return new(false, results.ToString(), $"COVER_BATCH_ABORTED {aborted}\n", 1);

        CommandResult emission;
        try
        {
            emission = Emit(repositoryRoot, reportBundle);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            emission = new(false, string.Empty, $"COVER_BATCH_EMIT_FAILED {exception.Message}\n");
        }
        successful &= emission.Success;
        return new(successful, results + emission.Output, emission.Error, successful ? 0 : 1);
    }

    private static void Render(StringBuilder output, BatchItem item, string status, string reason) =>
        output.Append("COVER_BATCH ").Append(JsonSerializer.Serialize(new
        {
            atom_id = item.AtomId,
            status,
            lines = item.Lines,
            reason,
        })).Append('\n');

    private static CommandResult Emit(string root, PrecomputedLeanReportSource.CapturedBundle? reportBundle)
    {
        reportBundle?.ValidateForEmission();
        var output = new StringWriter();
        var error = new StringWriter();
        var exit = ValuesEmitter.Emit(root, false, output, error);

        if (exit != 0) return new(false, output.ToString(), error.ToString());
        return new(true, output.ToString(), error.ToString());
    }

}
