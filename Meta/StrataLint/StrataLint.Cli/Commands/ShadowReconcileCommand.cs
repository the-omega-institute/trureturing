using System.Text.Json;

namespace StrataLint.Cli;

internal sealed record ShadowRecord(int PrNumber, long RunId, int RunAttempt, string HeadSha, string Outcome, double? WallSeconds);
internal sealed record ShadowJob(int PrNumber, long RunId, int RunAttempt, bool Terminal, IReadOnlyList<ShadowRecord> Records);
internal sealed record ShadowReconcileResult(bool WindowClosed, bool Halted, string? HaltReason, int N, int HitCount, double HitRate, double AmortisedMissSeconds, double MaxMissSeconds);

internal static class ShadowReconciler
{
    internal static ShadowReconcileResult Reconcile(IEnumerable<ShadowJob> jobs, int windowSize = 40)
    {
        var members = jobs.OrderBy(j => j.RunId).ThenBy(j => j.RunAttempt).GroupBy(j => j.PrNumber).Select(g => g.First()).Take(windowSize).ToArray();
        var closed = members.Length == windowSize;
        var selected = members.Select(m => m with { Records = m.Records.Where(r => r.RunId == m.RunId && r.RunAttempt == 1).ToArray() }).ToArray();
        var bad = selected.FirstOrDefault(m => !m.Terminal || m.Records.Count(r => r.Outcome is "hit" or "miss") != 1);
        if (bad is not null) return new(false, true, $"PR #{bad.PrNumber}: job terminal/record reconciliation failed", selected.Length, 0, 0, 0, 0);
        var records = selected.Select(m => m.Records.Single(r => r.Outcome is "hit" or "miss")).ToArray();
        var hits = records.Count(r => r.Outcome == "hit");
        var misses = records.Where(r => r.Outcome == "miss").ToArray();
        var budget = misses.Sum(r => r.WallSeconds ?? double.NaN) / records.Length;
        var max = misses.Length == 0 ? 0 : misses.Max(r => r.WallSeconds ?? double.NaN);
        string? reason = hits / (double)records.Length < .8 ? "hit rate below 80%" : budget > 30 ? "amortised miss budget above 30.0s/PR" : max > 180 ? "single miss above 180.0s" : null;
        return new(closed, reason is not null, reason, records.Length, hits, hits / (double)records.Length, budget, max);
    }
}

internal static class ShadowReconcileCommand
{
    internal static CommandResult Run(IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count != 1) throw new InvalidOperationException("USAGE: shadow-reconcile <jobs.json>");
            var jobs = JsonSerializer.Deserialize<List<ShadowJob>>(File.ReadAllText(arguments[0])) ?? throw new InvalidOperationException("empty input");
            return new(true, JsonSerializer.Serialize(ShadowReconciler.Reconcile(jobs)), string.Empty);
        }
        catch (Exception e) when (e is IOException or JsonException or InvalidOperationException)
        { return new(false, string.Empty, $"INFRASTRUCTURE_FAILURE shadow-reconcile: {e.Message}\n"); }
    }
}
