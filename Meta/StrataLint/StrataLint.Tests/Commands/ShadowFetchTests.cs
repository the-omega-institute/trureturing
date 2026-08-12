using System.IO.Compression;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class ShadowFetchTests
{
    [Fact]
    public void WorkflowRunQueryFiltersPullRequestTargetEvent()
    {
        var requests = new List<Uri>();
        using var client = new HttpClient(new RecordingHandler(requests));
        var fetcher = new ShadowGitHubFetcher(client, new Uri("https://api.example/"));

        fetcher.Fetch("owner/repository", "ci.yml");

        Assert.Equal(
            new Uri("https://api.example/repos/owner/repository/actions/workflows/ci.yml/runs?event=pull_request_target&per_page=100&page=1"),
            requests[0]);
    }

    [Fact]
    public void ArtifactResponseConvertsToShadowJob()
    {
        var run = new ShadowRunSnapshot(101, 1, 17, true);
        var artifact = "{\"pr_number\":17,\"head_sha\":\"abc\",\"run_id\":101,\"run_attempt\":1,\"outcome\":\"hit\",\"wall_seconds\":null,\"address\":\"deadbeef\"}";

        var job = ShadowJobConverter.FromArtifact(run, artifact);

        Assert.Equal(17, job.PrNumber);
        Assert.Equal(101, job.RunId);
        Assert.True(job.Terminal);
        Assert.Single(job.Records);
        Assert.Equal("hit", job.Records[0].Outcome);
    }

    [Fact]
    public void ApiNullPullRequestNumberAcceptsAndUsesArtifactPullRequestNumber()
    {
        var run = new ShadowRunSnapshot(31595677784, 1, null, true, "merged-head");
        var artifact = "{\"pr_number\":1421,\"head_sha\":\"merged-head\",\"run_id\":31595677784,\"run_attempt\":1,\"outcome\":\"hit\",\"wall_seconds\":null,\"address\":\"runtime-fact\"}";

        var job = ShadowJobConverter.FromArtifact(run, artifact);

        Assert.Equal(1421, job.PrNumber);
        Assert.Equal(1421, Assert.Single(job.Records).PrNumber);
    }

    [Fact]
    public void ApiPullRequestNumberMismatchWithArtifactIsRejected()
    {
        var run = new ShadowRunSnapshot(31596893884, 1, 1433, true, "open-head");
        var artifact = "{\"pr_number\":1434,\"head_sha\":\"open-head\",\"run_id\":31596893884,\"run_attempt\":1,\"outcome\":\"hit\",\"wall_seconds\":null,\"address\":\"mismatched-pr\"}";

        var exception = Assert.Throws<JsonException>(() => ShadowJobConverter.FromArtifact(run, artifact));

        Assert.Equal("shadow artifact pull request does not match workflow run", exception.Message);
    }

    [Fact]
    public void ArtifactRunIdMismatchIsRejected()
    {
        var run = new ShadowRunSnapshot(501, 1, 51, true, "run-id-head");
        var artifact = "{\"pr_number\":51,\"head_sha\":\"run-id-head\",\"run_id\":502,\"run_attempt\":1,\"outcome\":\"hit\",\"wall_seconds\":null,\"address\":\"mismatched-run\"}";

        var exception = Assert.Throws<JsonException>(() => ShadowJobConverter.FromArtifact(run, artifact));

        Assert.Equal("shadow artifact identity does not match workflow run", exception.Message);
    }

    [Fact]
    public void ArtifactRunAttemptMismatchIsRejected()
    {
        var run = new ShadowRunSnapshot(503, 1, 52, true, "attempt-head");
        var artifact = "{\"pr_number\":52,\"head_sha\":\"attempt-head\",\"run_id\":503,\"run_attempt\":2,\"outcome\":\"hit\",\"wall_seconds\":null,\"address\":\"mismatched-attempt\"}";

        var exception = Assert.Throws<JsonException>(() => ShadowJobConverter.FromArtifact(run, artifact));

        Assert.Equal("shadow artifact identity does not match workflow run", exception.Message);
    }

    [Fact]
    public void FailedArtifactOutcomeConvertsWithFailureFields()
    {
        var run = new ShadowRunSnapshot(102, 2, 18, true);
        var artifact = "{\"pr_number\":18,\"head_sha\":\"def\",\"run_id\":102,\"run_attempt\":2,\"outcome\":\"miss-error\",\"wall_seconds\":12.5,\"address\":\"cafebabe\",\"stage\":\"produce\",\"exit_code\":1}";

        var job = ShadowJobConverter.FromArtifact(run, artifact);

        Assert.Single(job.Records);
        Assert.Equal("miss-error", job.Records[0].Outcome);
        Assert.Equal(12.5, job.Records[0].WallSeconds);
    }

    [Fact]
    public void MissingRequiredArtifactFieldIsRejected()
    {
        var run = new ShadowRunSnapshot(103, 1, 19, true);
        var artifact = "{\"pr_number\":19,\"head_sha\":\"abc\",\"run_id\":103,\"run_attempt\":1,\"wall_seconds\":null,\"address\":\"deadbeef\"}";

        Assert.Throws<JsonException>(() => ShadowJobConverter.FromArtifact(run, artifact));
    }

    [Fact]
    public void FailedArtifactWithoutFailureFieldsIsRejected()
    {
        var run = new ShadowRunSnapshot(104, 1, 20, true);
        var artifact = "{\"pr_number\":20,\"head_sha\":\"abc\",\"run_id\":104,\"run_attempt\":1,\"outcome\":\"hit-error\",\"wall_seconds\":null,\"address\":\"deadbeef\"}";

        Assert.Throws<JsonException>(() => ShadowJobConverter.FromArtifact(run, artifact));
    }

    [Fact]
    public void NoRecordArtifactConvertsToExplicitOutcome()
    {
        var run = new ShadowRunSnapshot(105, 1, 25, true);
        var artifact = "{\"pr_number\":25,\"head_sha\":\"abc\",\"run_id\":105,\"run_attempt\":1,\"outcome\":\"no-record\",\"wall_seconds\":null,\"address\":\"unknown\",\"stage\":\"unreported-step\",\"exit_code\":null}";

        var job = ShadowJobConverter.FromArtifact(run, artifact);

        Assert.Equal("no-record", Assert.Single(job.Records).Outcome);
    }

    [Fact]
    public void RunPageParserAggregatesPagesAndPullRequestNumbers()
    {
        var first = "{\"workflow_runs\":[{\"id\":201,\"run_attempt\":1,\"status\":\"completed\",\"conclusion\":\"success\",\"pull_requests\":[{\"number\":21}]}]}";
        var second = "{\"workflow_runs\":[{\"id\":202,\"run_attempt\":1,\"status\":\"in_progress\",\"conclusion\":null,\"pull_requests\":[{\"number\":22}]}]}";

        var runs = ShadowGitHubJson.ParseRunPages(new[] { first, second });

        Assert.Equal(2, runs.Count);
        Assert.Equal(21, runs[0].PrNumber);
        Assert.True(runs[0].Terminal);
        Assert.False(runs[1].Terminal);
    }

    [Fact]
    public void JobPageParserReadsShadowJobTerminalState()
    {
        var page = "{\"jobs\":[{\"name\":\"old-side-report-shadow\",\"status\":\"completed\",\"conclusion\":\"failure\"}]}";

        Assert.True(ShadowGitHubJson.ParseJobTerminal(new[] { page }));
    }

    [Fact]
    public void JobPageParserTreatsMissingShadowJobAsNonTerminal()
    {
        var page = "{\"jobs\":[{\"name\":\"other-job\",\"status\":\"completed\",\"conclusion\":\"success\"}]}";

        Assert.False(ShadowGitHubJson.ParseJobTerminal(new[] { page }));
    }

    [Fact]
    public void MissingArtifactStillProducesTerminalJobWithZeroRecords()
    {
        var run = new ShadowRunSnapshot(301, 1, 31, true);

        var job = ShadowJobConverter.FromArtifact(run, null);

        Assert.Equal(31, job.PrNumber);
        Assert.True(job.Terminal);
        Assert.Empty(job.Records);
    }

    [Fact]
    public void NonTerminalJobWithArtifactRemainsNonTerminal()
    {
        var run = new ShadowRunSnapshot(302, 1, 32, false);
        var artifact = "{\"pr_number\":32,\"head_sha\":\"abc\",\"run_id\":302,\"run_attempt\":1,\"outcome\":\"hit\",\"wall_seconds\":null,\"address\":\"deadbeef\"}";

        var job = ShadowJobConverter.FromArtifact(run, artifact);

        Assert.False(job.Terminal);
        Assert.Single(job.Records);
    }

    [Fact]
    public void AggregateIncludesRunWithoutArtifactAsEmptyTerminalJob()
    {
        var runs = new[]
        {
            new ShadowRunSnapshot(401, 1, 41, true, "abc"),
            new ShadowRunSnapshot(402, 1, 42, true, "def"),
        };
        var artifacts = new Dictionary<(long, int), string?>
        {
            [(401, 1)] = "{\"pr_number\":41,\"head_sha\":\"abc\",\"run_id\":401,\"run_attempt\":1,\"outcome\":\"hit\",\"wall_seconds\":null,\"address\":\"a\"}",
        };

        var jobs = ShadowJobConverter.Aggregate(runs, artifacts);

        Assert.Equal(2, jobs.Count);
        Assert.Single(jobs[0].Records);
        Assert.Empty(jobs[1].Records);
        Assert.True(jobs[1].Terminal);
    }

    [Fact]
    public void ArtifactHeadShaMismatchIsRejected()
    {
        var run = new ShadowRunSnapshot(403, 1, 43, true, "expected");
        var artifact = "{\"pr_number\":43,\"head_sha\":\"actual\",\"run_id\":403,\"run_attempt\":1,\"outcome\":\"hit\",\"wall_seconds\":null,\"address\":\"a\"}";

        var exception = Assert.Throws<JsonException>(() => ShadowJobConverter.FromArtifact(run, artifact));

        Assert.Equal("shadow artifact head_sha does not match workflow run", exception.Message);
    }

    [Fact]
    public void FetchIncludesApiNullPullRequestRunWhenArtifactExists()
    {
        var requests = new List<Uri>();
        using var archive = new MemoryStream();
        using (var zip = new ZipArchive(archive, ZipArchiveMode.Create, leaveOpen: true))
        {
            var entry = zip.CreateEntry("old-side-shadow-record.json");
            using var writer = new StreamWriter(entry.Open(), Encoding.UTF8);
            writer.Write("{\"pr_number\":1421,\"head_sha\":\"merged-head\",\"run_id\":31595677784,\"run_attempt\":1,\"outcome\":\"hit\",\"wall_seconds\":null,\"address\":\"runtime-fact\"}");
        }
        using var client = new HttpClient(new ApiNullArtifactHandler(requests, archive.ToArray()));
        var fetcher = new ShadowGitHubFetcher(client, new Uri("https://api.example/"));

        var jobs = fetcher.Fetch("owner/repository", "ci.yml");

        var job = Assert.Single(jobs);
        Assert.Equal(1421, job.PrNumber);
        Assert.Contains(requests, request => request.AbsolutePath == "/repos/owner/repository/actions/runs/31595677784/attempts/1/jobs");
    }

    private sealed class RecordingHandler(List<Uri> requests) : HttpMessageHandler
    {
        protected override Task<HttpResponseMessage> SendAsync(HttpRequestMessage request, CancellationToken cancellationToken)
        {
            requests.Add(request.RequestUri!);
            var body = request.RequestUri!.AbsolutePath.EndsWith("/runs", StringComparison.Ordinal)
                ? "{\"total_count\":0,\"workflow_runs\":[]}"
                : "{\"total_count\":0,\"artifacts\":[]}";
            return Task.FromResult(new HttpResponseMessage(System.Net.HttpStatusCode.OK)
            {
                Content = new StringContent(body),
            });
        }
    }

    private sealed class ApiNullArtifactHandler(List<Uri> requests, byte[] archive) : HttpMessageHandler
    {
        protected override Task<HttpResponseMessage> SendAsync(HttpRequestMessage request, CancellationToken cancellationToken)
        {
            requests.Add(request.RequestUri!);
            HttpContent content = request.RequestUri!.AbsolutePath switch
            {
                "/repos/owner/repository/actions/workflows/ci.yml/runs" => new StringContent("{\"total_count\":1,\"workflow_runs\":[{\"id\":31595677784,\"run_attempt\":1,\"status\":\"completed\",\"head_sha\":\"merged-head\",\"pull_requests\":[]}]}"),
                "/repos/owner/repository/actions/artifacts" => new StringContent("{\"total_count\":1,\"artifacts\":[{\"name\":\"old-side-shadow-record-31595677784-1\",\"expired\":false,\"archive_download_url\":\"https://api.example/artifacts/31595677784\"}]}"),
                "/repos/owner/repository/actions/runs/31595677784/attempts/1/jobs" => new StringContent("{\"total_count\":1,\"jobs\":[{\"name\":\"old-side-report-shadow\",\"status\":\"completed\"}]}"),
                "/artifacts/31595677784" => new ByteArrayContent(archive),
                _ => throw new InvalidOperationException($"unexpected request {request.RequestUri}"),
            };
            return Task.FromResult(new HttpResponseMessage(System.Net.HttpStatusCode.OK) { Content = content });
        }
    }
}
