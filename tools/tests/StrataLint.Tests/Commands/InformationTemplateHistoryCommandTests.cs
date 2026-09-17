using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using File = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

public sealed class InformationTemplateHistoryCommandTests
{
    [Fact]
    public void inactive_command_reads_only_predicate_and_never_produces()
    {
        using var fixture = new InformationTemplateHistoryFixture();
        var result = fixture.Command("plan", "--protected-base", fixture.Head, "--output", fixture.Plan);
        Assert.True(result.Success, "[FAIL] inactive_command_reads_only_predicate_and_never_produces: " + result.Error);
        using var plan = JsonDocument.Parse(File.ReadAllBytes(fixture.Plan));
        Assert.False(plan.RootElement.GetProperty("required").GetBoolean());
        Assert.Equal(0, fixture.CandidateReads);
        Assert.Equal(0, fixture.HistoricalReads);
        Assert.Equal(0, fixture.Productions);
    }

    [Fact]
    public void prepare_materializes_snapshot_origins_and_private_index()
    {
        using var fixture = new InformationTemplateHistoryFixture();
        fixture.SeedPlan();
        var result = fixture.Command("prepare", "--plan", fixture.Plan, "--revision", fixture.Seed, "--work", fixture.Work);
        Assert.True(result.Success, "[FAIL] prepare_materializes_snapshot_origins_and_private_index: " + result.Error);
        Assert.Equal("-- historical root\n", File.ReadAllText(Path.Combine(fixture.Work, "Trureturing.lean")));
        Assert.Equal("-- historical content\n", File.ReadAllText(Path.Combine(fixture.Work, "D5/S0/Carrier/History.lean")));
        Assert.Equal("historical state", File.ReadAllText(Path.Combine(fixture.Work, "Golden/Frozen/state/probe.lean.json")));
        Assert.Equal("#!/bin/sh\n# candidate inspector\n", File.ReadAllText(Path.Combine(fixture.Work, "tools/lean-inspector/inspect.sh")));
        Assert.Equal("candidate runtime", File.ReadAllText(Path.Combine(fixture.Work, "tools/StrataLint.Scribe/Fixture.cs")));
        Assert.False(File.Exists(Path.Combine(fixture.Work, "Meta/lean-report.toml")));
        Assert.False(File.Exists(Path.Combine(fixture.Work, "D5/S0/Carrier/Candidate.lean")));
        var indexed = GitRepositorySnapshotReader.ReadCurrent(fixture.Work);
        Assert.Contains(indexed.Entries, e => e.Path == "tools/StrataLint.Scribe/Fixture.cs");
        Assert.DoesNotContain(indexed.Entries, e => e.Path.Split('/').Any(p => p is ".lake" or "bin" or "obj"));
        Assert.Equal("", ReviewRegressionTests.RunGit(fixture.Work, "remote"));
        Assert.Equal(0, fixture.Productions);
    }

    [Fact]
    public void production_validates_before_publication_and_hit_runs_zero_inspectors()
    {
        using var fixture = new InformationTemplateHistoryFixture();
        fixture.SeedPlan();
        var first = fixture.Produce();
        Assert.True(first.Success, "[FAIL] production_validates_before_publication_and_hit_runs_zero_inspectors: " + first.Error);
        Assert.Equal(1, fixture.Productions);
        Assert.True(File.Exists(Path.Combine(fixture.Output, "history.json")));
        Assert.True(fixture.Produce().Success);
        Assert.Equal(1, fixture.Productions);
        Assert.True(fixture.Validate().Success);
        Assert.Equal(1, fixture.Productions);
        Assert.Equal(fixture.Work, fixture.ProducerCwd);
        Assert.Contains(Path.Combine(fixture.Work, "tools/lean-inspector/inspect.sh"), fixture.ProducerArguments);
    }

    [Fact]
    public void failure_and_timeout_publish_no_complete_bundle()
    {
        foreach (var timeout in new[] { false, true })
        {
            using var fixture = new InformationTemplateHistoryFixture();
            fixture.SeedPlan();
            fixture.FailProducer = !timeout;
            fixture.TimeoutProducer = timeout;
            var result = fixture.Produce();
            Assert.False(result.Success);
            Assert.Contains(timeout ? "fixture timeout" : "exit=19", result.Error);
            Assert.False(File.Exists(Path.Combine(fixture.Output, "history.json")));
        }
    }

    [Fact]
    public void stale_or_incomplete_bundle_cannot_validate_or_hit()
    {
        foreach (var member in new[] { "raw-lean-report.json", "raw-lean-report.json.sha256",
            "raw-lean-report.json.input.attestation", "raw-lean-report.json.provenance.json",
            "raw-lean-report.json.materials.zip", "history.json" })
        {
            using var fixture = new InformationTemplateHistoryFixture();
            fixture.SeedPlan();
            Assert.True(fixture.Produce().Success);
            File.WriteAllText(Path.Combine(fixture.Output, member), "corrupt");
            using var plan = JsonDocument.Parse(File.ReadAllBytes(fixture.Plan));
            File.WriteAllText(Path.Combine(fixture.Scratch.Path, "cache",
                plan.RootElement.GetProperty("producer").GetString()!, fixture.Seed, member), "corrupt");
            Assert.False(fixture.Validate().Success);
            Assert.True(fixture.Produce().Success);
            Assert.Equal(2, fixture.Productions);
        }
    }

    [Fact]
    public void source_changes_preserve_P_and_producer_changes_invalidate_plan()
    {
        using var fixture = new InformationTemplateHistoryFixture();
        fixture.SeedPlan();
        var first = File.ReadAllText(fixture.Plan);
        fixture.Candidate["D5/S0/Carrier/Candidate.lean"] += "-- extra candidate content\n";
        fixture.SeedPlan();
        Assert.Equal(first, File.ReadAllText(fixture.Plan));
        fixture.Candidate["tools/StrataLint.Scribe/Fixture.cs"] += "changed";
        Assert.False(fixture.Produce().Success);
        fixture.SeedPlan();
        Assert.NotEqual(first, File.ReadAllText(fixture.Plan));
        Assert.True(fixture.Produce().Success);
    }

    [Fact]
    public void adoption_preserves_bundle_and_cannot_relabel_candidate_as_base()
    {
        using var fixture = new InformationTemplateHistoryFixture();
        fixture.SeedPlan();
        var candidate = Path.Combine(fixture.Scratch.Path, "candidate.json");
        InformationTemplateHistoryFixture.WriteBundle(candidate, fixture.CandidateSnapshot);
        var result = fixture.Command("adopt", "--plan", fixture.Plan, "--revision", fixture.Head,
            "--report", candidate, "--output", fixture.Output);
        Assert.True(result.Success, "[FAIL] adoption_preserves_bundle_and_cannot_relabel_candidate_as_base: " + result.Error);
        Assert.Equal(File.ReadAllBytes(candidate), File.ReadAllBytes(Path.Combine(fixture.Output, "raw-lean-report.json")));
        Assert.Equal(0, fixture.Productions);
        Assert.False(fixture.Command("adopt", "--plan", fixture.Plan, "--revision", fixture.Seed,
            "--report", candidate, "--output", fixture.Output).Success);
    }
}
