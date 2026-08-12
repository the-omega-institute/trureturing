using System.Text.Json;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class ShadowFetchTests
{
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

        Assert.Throws<JsonException>(() => ShadowJobConverter.FromArtifact(run, artifact));
    }
}
