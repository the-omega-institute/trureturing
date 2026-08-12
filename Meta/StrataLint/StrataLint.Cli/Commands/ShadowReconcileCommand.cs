using System.IO.Compression;
using System.Globalization;
using System.Text.Json;
using System.Text.RegularExpressions;

namespace StrataLint.Cli;

internal sealed record ShadowRecord(int PrNumber, long RunId, int RunAttempt, string HeadSha, string Outcome, double? WallSeconds);
internal sealed record ShadowJob(int PrNumber, long RunId, int RunAttempt, bool Terminal, IReadOnlyList<ShadowRecord> Records);
internal sealed record ShadowRunSnapshot(long RunId, int RunAttempt, int PrNumber, bool Terminal, string HeadSha = "");
internal sealed record ShadowReconcileResult(
    bool WindowClosed,
    bool Halted,
    string? HaltReason,
    int N,
    int HitCount,
    double HitRate,
    double AmortisedMissSeconds,
    double MaxMissSeconds)
{
    public string WindowStatus { get; init; } = "unknown";
}

internal static class ShadowJobConverter
{
    private static readonly HashSet<string> Outcomes = new(StringComparer.Ordinal)
    {
        "hit", "miss", "hit-error", "miss-error", "no-record",
    };

    internal static ShadowJob FromArtifact(ShadowRunSnapshot run, string? artifactJson)
    {
        if (artifactJson is null) return new(run.PrNumber, run.RunId, run.RunAttempt, run.Terminal, Array.Empty<ShadowRecord>());

        using var document = JsonDocument.Parse(artifactJson);
        var root = document.RootElement;
        var prNumber = RequiredInt(root, "pr_number");
        var runId = RequiredLong(root, "run_id");
        var runAttempt = RequiredInt(root, "run_attempt");
        var headSha = RequiredString(root, "head_sha");
        _ = RequiredString(root, "address");
        var outcome = RequiredString(root, "outcome");
        if (!Outcomes.Contains(outcome)) throw new JsonException($"unknown shadow outcome '{outcome}'");
        if (outcome is "hit-error" or "miss-error" or "no-record")
        {
            _ = RequiredString(root, "stage");
            if (!root.TryGetProperty("exit_code", out var exitCode) || exitCode.ValueKind is not (JsonValueKind.Number or JsonValueKind.Null))
                throw new JsonException("missing or invalid 'exit_code'");
        }
        if (!root.TryGetProperty("wall_seconds", out var wall) || wall.ValueKind is not (JsonValueKind.Number or JsonValueKind.Null))
            throw new JsonException("missing or invalid 'wall_seconds'");
        double? wallSeconds = wall.ValueKind == JsonValueKind.Number ? wall.GetDouble() : null;
        if (runId != run.RunId || runAttempt != run.RunAttempt)
            throw new JsonException("shadow artifact identity does not match workflow run");
        if (prNumber != run.PrNumber)
            throw new JsonException("shadow artifact pull request does not match workflow run");
        if (run.HeadSha.Length != 0 && !string.Equals(headSha, run.HeadSha, StringComparison.Ordinal))
            throw new JsonException("shadow artifact head_sha does not match workflow run");
        return new(run.PrNumber, run.RunId, run.RunAttempt, run.Terminal,
            new[] { new ShadowRecord(prNumber, runId, runAttempt, headSha, outcome, wallSeconds) });
    }

    internal static IReadOnlyList<ShadowJob> Aggregate(
        IEnumerable<ShadowRunSnapshot> runs,
        IReadOnlyDictionary<(long RunId, int Attempt), string?> artifacts)
    {
        return runs.Select(run =>
        {
            artifacts.TryGetValue((run.RunId, run.RunAttempt), out var artifactJson);
            return FromArtifact(run, artifactJson);
        }).ToArray();
    }

    private static int RequiredInt(JsonElement root, string name) =>
        root.TryGetProperty(name, out var value) && value.ValueKind == JsonValueKind.Number && value.TryGetInt32(out var result)
            ? result
            : throw new JsonException($"missing or invalid '{name}'");

    private static long RequiredLong(JsonElement root, string name) =>
        root.TryGetProperty(name, out var value) && value.ValueKind == JsonValueKind.Number && value.TryGetInt64(out var result)
            ? result
            : throw new JsonException($"missing or invalid '{name}'");

    private static string RequiredString(JsonElement root, string name) =>
        root.TryGetProperty(name, out var value) && value.ValueKind == JsonValueKind.String && value.GetString() is { } result
            ? result
            : throw new JsonException($"missing or invalid '{name}'");
}

internal static class ShadowGitHubJson
{
    internal static bool ParseJobTerminal(IEnumerable<string> pages)
    {
        foreach (var page in pages)
        {
            using var document = JsonDocument.Parse(page);
            if (!document.RootElement.TryGetProperty("jobs", out var jobs) || jobs.ValueKind != JsonValueKind.Array)
                throw new JsonException("GitHub jobs response has no jobs array");
            foreach (var job in jobs.EnumerateArray())
            {
                if (!job.TryGetProperty("name", out var name) || name.ValueKind != JsonValueKind.String) continue;
                var jobName = name.GetString();
                if (!string.Equals(jobName, "old-side-report-shadow", StringComparison.Ordinal) &&
                    !string.Equals(jobName, "Old-side Lean report shadow measurement", StringComparison.Ordinal)) continue;
                return job.TryGetProperty("status", out var status) && status.ValueKind == JsonValueKind.String &&
                    string.Equals(status.GetString(), "completed", StringComparison.OrdinalIgnoreCase);
            }
        }
        return false;
    }

    internal static IReadOnlyList<ShadowRunSnapshot> ParseRunPages(IEnumerable<string> pages)
    {
        var runs = new List<ShadowRunSnapshot>();
        foreach (var page in pages)
        {
            using var document = JsonDocument.Parse(page);
            if (!document.RootElement.TryGetProperty("workflow_runs", out var items) || items.ValueKind != JsonValueKind.Array)
                throw new JsonException("GitHub workflow runs response has no workflow_runs array");
            foreach (var item in items.EnumerateArray())
            {
                var runId = RequiredLong(item, "id");
                var attempt = item.TryGetProperty("run_attempt", out var attemptValue) && attemptValue.TryGetInt32(out var parsedAttempt) ? parsedAttempt : 1;
                var status = RequiredString(item, "status");
                var terminal = string.Equals(status, "completed", StringComparison.OrdinalIgnoreCase);
                var headSha = item.TryGetProperty("head_sha", out var sha) && sha.ValueKind == JsonValueKind.String ? sha.GetString() ?? string.Empty : string.Empty;
                var prNumber = 0;
                if (item.TryGetProperty("pull_requests", out var prs) && prs.ValueKind == JsonValueKind.Array)
                {
                    var first = prs.EnumerateArray().FirstOrDefault();
                    if (first.ValueKind == JsonValueKind.Object && first.TryGetProperty("number", out var number) && number.TryGetInt32(out var parsedNumber))
                        prNumber = parsedNumber;
                }
                runs.Add(new(runId, attempt, prNumber, terminal, headSha));
            }
        }
        return runs;
    }

    private static int RequiredInt(JsonElement root, string name) =>
        root.TryGetProperty(name, out var value) && value.TryGetInt32(out var result) ? result : throw new JsonException($"missing or invalid '{name}'");

    private static long RequiredLong(JsonElement root, string name) =>
        root.TryGetProperty(name, out var value) && value.TryGetInt64(out var result) ? result : throw new JsonException($"missing or invalid '{name}'");

    private static string RequiredString(JsonElement root, string name) =>
        root.TryGetProperty(name, out var value) && value.ValueKind == JsonValueKind.String && value.GetString() is { } result ? result : throw new JsonException($"missing or invalid '{name}'");
}

internal sealed class ShadowGitHubFetcher
{
    private const string ArtifactPrefix = "old-side-shadow-record-";
    private static readonly Regex ArtifactName = new($"^{Regex.Escape(ArtifactPrefix)}(?<run>\\d+)-(?<attempt>\\d+)$", RegexOptions.CultureInvariant | RegexOptions.Compiled);
    private readonly HttpClient client;
    private readonly Uri apiRoot;

    internal ShadowGitHubFetcher(HttpClient client, Uri? apiRoot = null)
    {
        this.client = client;
        this.apiRoot = apiRoot ?? new Uri("https://api.github.com/", UriKind.Absolute);
    }

    internal IReadOnlyList<ShadowJob> Fetch(string repository, string workflow)
    {
        var pages = GetPages($"repos/{repository}/actions/workflows/{Uri.EscapeDataString(workflow)}/runs?event=pull_request&per_page=100");
        var runs = ShadowGitHubJson.ParseRunPages(pages).Where(run => run.PrNumber > 0)
            .Select(run => run with { Terminal = FetchJobTerminal(repository, run) }).ToArray();
        var artifactUrls = FetchArtifacts(repository);
        var artifactJson = artifactUrls.ToDictionary(item => item.Key, item => (string?)ReadArtifactJson(item.Value));
        return ShadowJobConverter.Aggregate(runs, artifactJson);
    }

    private Dictionary<(long RunId, int Attempt), Uri> FetchArtifacts(string repository)
    {
        var result = new Dictionary<(long, int), Uri>();
        foreach (var page in GetPages($"repos/{repository}/actions/artifacts?per_page=100"))
        {
            using var document = JsonDocument.Parse(page);
            if (!document.RootElement.TryGetProperty("artifacts", out var items) || items.ValueKind != JsonValueKind.Array)
                throw new JsonException("GitHub artifacts response has no artifacts array");
            foreach (var item in items.EnumerateArray())
            {
                if (!item.TryGetProperty("name", out var nameValue) || nameValue.ValueKind != JsonValueKind.String) continue;
                var match = ArtifactName.Match(nameValue.GetString() ?? string.Empty);
                if (!match.Success || item.TryGetProperty("expired", out var expired) && expired.ValueKind == JsonValueKind.True) continue;
                if (!item.TryGetProperty("archive_download_url", out var urlValue) || urlValue.ValueKind != JsonValueKind.String) throw new JsonException("shadow artifact has no archive_download_url");
                result[(long.Parse(match.Groups["run"].Value, CultureInfo.InvariantCulture), int.Parse(match.Groups["attempt"].Value, CultureInfo.InvariantCulture))] = new Uri(urlValue.GetString()!, UriKind.Absolute);
            }
        }
        return result;
    }

    private bool FetchJobTerminal(string repository, ShadowRunSnapshot run)
    {
        var path = $"repos/{repository}/actions/runs/{run.RunId}/attempts/{run.RunAttempt}/jobs?per_page=100";
        return ShadowGitHubJson.ParseJobTerminal(GetPages(path));
    }

    private string ReadArtifactJson(Uri url)
    {
        using var response = client.GetAsync(url).GetAwaiter().GetResult();
        response.EnsureSuccessStatusCode();
        using var archive = new ZipArchive(response.Content.ReadAsStreamAsync().GetAwaiter().GetResult(), ZipArchiveMode.Read);
        var entry = archive.Entries.SingleOrDefault(candidate => candidate.Name.EndsWith(".json", StringComparison.OrdinalIgnoreCase));
        if (entry is null) throw new JsonException("shadow artifact archive contains no JSON");
        using var reader = new StreamReader(entry.Open());
        return reader.ReadToEnd();
    }

    private IEnumerable<string> GetPages(string relativePath)
    {
        for (var page = 1; ; page++)
        {
            var separator = relativePath.Contains('?', StringComparison.Ordinal) ? '&' : '?';
            var uri = new Uri(apiRoot, relativePath + $"{separator}page={page}");
            using var response = client.GetAsync(uri).GetAwaiter().GetResult();
            response.EnsureSuccessStatusCode();
            var body = response.Content.ReadAsStringAsync().GetAwaiter().GetResult();
            yield return body;
            using var document = JsonDocument.Parse(body);
            var property = document.RootElement.EnumerateObject().FirstOrDefault(item => item.Value.ValueKind == JsonValueKind.Array);
            if (property.Value.ValueKind != JsonValueKind.Array || property.Value.GetArrayLength() == 0) yield break;
            if (document.RootElement.TryGetProperty("total_count", out var total) && total.TryGetInt32(out var count) && page * 100 >= count) yield break;
        }
    }
}

internal static class ShadowReconciler
{
    internal static ShadowReconcileResult Reconcile(IEnumerable<ShadowJob> jobs, int windowSize = 40)
    {
        var members = jobs.OrderBy(j => j.RunId).ThenBy(j => j.RunAttempt).GroupBy(j => j.PrNumber).Select(g => g.First()).Take(windowSize).ToArray();
        var closed = members.Length == windowSize;
        var selected = members.Select(m => m with { Records = m.Records.Where(r => r.RunId == m.RunId && r.RunAttempt == 1).ToArray() }).ToArray();
        var bad = selected.FirstOrDefault(m => !m.Terminal || m.Records.Count(r => r.Outcome is "hit" or "miss") != 1);
        if (bad is not null) return new ShadowReconcileResult(false, true, $"PR #{bad.PrNumber}: job terminal/record reconciliation failed", selected.Length, 0, 0, 0, 0) { WindowStatus = "invalid" };
        var records = selected.Select(m => m.Records.Single(r => r.Outcome is "hit" or "miss")).ToArray();
        if (records.Length == 0) return new ShadowReconcileResult(false, false, null, 0, 0, 0, 0, 0) { WindowStatus = "not-started" };
        var hits = records.Count(r => r.Outcome == "hit");
        var misses = records.Where(r => r.Outcome == "miss").ToArray();
        var missingMissDuration = misses.FirstOrDefault(r => r.WallSeconds is null || !double.IsFinite(r.WallSeconds.Value));
        if (missingMissDuration is not null)
            return new ShadowReconcileResult(false, true, $"PR #{missingMissDuration.PrNumber}: miss record has no finite wall_seconds", records.Length, hits, 0, 0, 0) { WindowStatus = "invalid" };
        var budget = misses.Sum(r => r.WallSeconds!.Value) / records.Length;
        if (!double.IsFinite(budget))
            return new ShadowReconcileResult(false, true, "miss duration total is not finite", records.Length, hits, 0, 0, 0) { WindowStatus = "invalid" };
        var max = misses.Length == 0 ? 0 : misses.Max(r => r.WallSeconds!.Value);
        string? reason = hits / (double)records.Length < .8 ? "hit rate below 80%" : budget > 30 ? "amortised miss budget above 30.0s/PR" : max > 180 ? "single miss above 180.0s" : null;
        return new ShadowReconcileResult(closed, reason is not null, reason, records.Length, hits, hits / (double)records.Length, budget, max) { WindowStatus = closed ? "closed" : "open" };
    }
}

internal static class ShadowReconcileCommand
{
    internal static CommandResult Run(IReadOnlyList<string> arguments)
    {
        try
        {
            IReadOnlyList<ShadowJob> jobs;
            if (arguments.Count == 1)
            {
                jobs = JsonSerializer.Deserialize<List<ShadowJob>>(File.ReadAllText(arguments[0])) ?? throw new InvalidOperationException("empty input");
            }
            else if (arguments.Count == 3 && string.Equals(arguments[0], "--github", StringComparison.Ordinal))
            {
                jobs = FetchFromGitHub(arguments[1], arguments[2]);
            }
            else
            {
                throw new InvalidOperationException("USAGE: shadow-reconcile <jobs.json> | shadow-reconcile --github <owner/repository> <workflow>");
            }
            return new(true, JsonSerializer.Serialize(ShadowReconciler.Reconcile(jobs)), string.Empty);
        }
        catch (Exception e) when (e is IOException or JsonException or InvalidOperationException)
        { return new(false, string.Empty, $"INFRASTRUCTURE_FAILURE shadow-reconcile: {e.Message}\n"); }
    }

    private static IReadOnlyList<ShadowJob> FetchFromGitHub(string repository, string workflow)
    {
        var token = Environment.GetEnvironmentVariable("GITHUB_TOKEN") ?? Environment.GetEnvironmentVariable("GH_TOKEN");
        if (string.IsNullOrWhiteSpace(token)) throw new InvalidOperationException("GITHUB_TOKEN or GH_TOKEN is required for --github mode");
        using var client = new HttpClient();
        client.DefaultRequestHeaders.UserAgent.ParseAdd("StrataLint-shadow-reconcile");
        client.DefaultRequestHeaders.Accept.ParseAdd("application/vnd.github+json");
        client.DefaultRequestHeaders.Authorization = new System.Net.Http.Headers.AuthenticationHeaderValue("Bearer", token);
        var apiUrl = Environment.GetEnvironmentVariable("GITHUB_API_URL");
        var root = string.IsNullOrWhiteSpace(apiUrl) ? null : new Uri(apiUrl.TrimEnd('/') + "/", UriKind.Absolute);
        return new ShadowGitHubFetcher(client, root).Fetch(repository, workflow);
    }
}
