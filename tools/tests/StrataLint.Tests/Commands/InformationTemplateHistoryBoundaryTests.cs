using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;
using File = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

public sealed class InformationTemplateHistoryBoundaryTests
{
    [Fact]
    public void bundle_symlinks_cannot_validate_as_regular_members()
    {
        using var fixture = new InformationTemplateHistoryFixture();
        fixture.SeedPlan();
        Assert.True(fixture.Produce().Success);
        var member = Path.Combine(fixture.Output, "history.json");
        var target = Path.Combine(fixture.Scratch.Path, "metadata.json");
        File.WriteAllBytes(target, File.ReadAllBytes(member));
        File.Delete(member);
        new FileInfo(member).CreateAsSymbolicLink(target);
        Assert.False(fixture.Validate().Success);
        File.Delete(member);
        File.WriteAllBytes(member, File.ReadAllBytes(target));
        var alias = Path.Combine(fixture.Scratch.Path, "alias");
        Directory.CreateSymbolicLink(alias, fixture.Output);
        Assert.False(fixture.Command("validate", "--plan", fixture.Plan, "--revision", fixture.Seed, "--bundle", alias).Success);
    }

    [Fact]
    public void cache_hit_rechecks_producer_after_pair_lock()
    {
        using var fixture = new InformationTemplateHistoryFixture();
        fixture.SeedPlan();
        Assert.True(fixture.Produce().Success);
        fixture.AfterCandidateRead = () =>
        {
            fixture.AfterCandidateRead = null;
            fixture.Candidate["tools/StrataLint.Scribe/Fixture.cs"] += "edited after initial snapshot";
        };
        var result = fixture.Produce();
        Assert.False(result.Success);
        Assert.Contains("producer changed", result.Error);
        Assert.Equal(1, fixture.Productions);
    }

    [Fact]
    public void producer_selection_is_independent_of_content_and_binds_entire_registered_runtime()
    {
        using var fixture = new InformationTemplateHistoryFixture();
        string Address(Dictionary<string, string> files) => new InformationTemplateHistoryInputs(
            InformationTemplateHistoryFixture.Raw(files)).Producer;
        var first = Address(fixture.Candidate);
        foreach (var path in new[] { "Trureturing.lean", "D5/S0/Carrier/History.lean", "Golden/Frozen/state/probe.lean.json",
            InformationTemplateDebtStore.ActivationPath, "Golden/InformationTemplateDebt/rows/new.json" })
        {
            var changed = new Dictionary<string, string>(fixture.Candidate) { [path] = "content changes" };
            Assert.Equal(first, Address(changed));
        }
        foreach (var path in new[] { "tools/lean-inspector/inspect.sh", "tools/StrataLint.Cli/Fixture.cs",
            "tools/StrataLint.Scribe/Fixture.cs", "lean-toolchain", "lake-manifest.json", "lakefile.toml", ".gitignore",
            "Meta/lean-report.toml", "tools/new-helper.sh" })
        {
            var changed = new Dictionary<string, string>(fixture.Candidate) { [path] = "producer changes" };
            Assert.NotEqual(first, Address(changed));
        }
        var deleted = new Dictionary<string, string>(fixture.Candidate);
        deleted.Remove("tools/StrataLint.Scribe/Fixture.cs");
        Assert.NotEqual(first, Address(deleted));
        var mode = InformationTemplateHistoryFixture.Raw(fixture.Candidate);
        Assert.NotEqual(first, new InformationTemplateHistoryInputs(RawRepositorySnapshot.Create(mode.Entries.Select(e =>
            e.Path == "tools/lean-inspector/inspect.sh" ? e with { GitMode = "100755" } : e))).Producer);
    }

    [Fact]
    public void selected_aliases_escapes_and_historical_executable_config_are_rejected()
    {
        using var fixture = new InformationTemplateHistoryFixture();
        var current = InformationTemplateHistoryFixture.Raw(fixture.Candidate);
        Assert.Throws<FormatException>(() => new InformationTemplateHistoryInputs(RawRepositorySnapshot.Create(current.Entries.Select(e =>
            e.Path == "tools/lean-inspector/inspect.sh" ? e with { GitMode = "120000" } : e))));
        foreach (var path in new[] { "../escape", "tools/.lake/config", "tools/bin/old", "tools/obj/old", "tools/.git/config" })
            Assert.Throws<FormatException>(() => InformationTemplateHistoryInputs.Plain(RawRepositoryEntry.FromText(path, "x")));
        var inputs = new InformationTemplateHistoryInputs(current);
        fixture.Historical["lakefile.lean"] = "historical executable";
        Assert.Contains("unsupported executable input", Assert.Throws<FormatException>(() => inputs.Material(fixture.Seed,
            InformationTemplateHistoryFixture.Raw(fixture.Historical))).Message);
        fixture.Historical.Remove("lakefile.lean");
        fixture.Historical["tools/lean-inspector/retired.lean"] = "old script";
        var material = inputs.Material(fixture.Seed, InformationTemplateHistoryFixture.Raw(fixture.Historical));
        Assert.DoesNotContain(material.Files, f => f.Path.EndsWith("retired.lean", StringComparison.Ordinal));
    }

    [Fact]
    public void original_source_mismatch_and_missing_objects_are_explicit_errors()
    {
        using var fixture = new InformationTemplateHistoryFixture();
        fixture.SeedPlan();
        Assert.True(fixture.Produce().Success);
        fixture.Historical["D5/S0/Carrier/History.lean"] += "-- wrong revision bytes\n";
        Assert.False(fixture.Validate().Success);
        fixture.Candidate[InformationTemplateDebtStore.ActivationPath] = DeclaredTemplateReviewTests.Text(
            InformationTemplateDebtStore.WriteActivation(new(new string('d', 40), false)));
        var missing = fixture.Command("plan", "--protected-base", fixture.Head, "--purpose", "seed");
        Assert.False(missing.Success);
        Assert.Contains("missing historical object", missing.Error);
    }

    [Fact]
    public void cache_save_failure_preserves_valid_current_artifact()
    {
        using var fixture = new InformationTemplateHistoryFixture();
        fixture.SeedPlan();
        var cache = Path.Combine(fixture.Scratch.Path, "unavailable-cache");
        File.WriteAllText(cache, "not a directory");
        var result = fixture.Command("produce", "--plan", fixture.Plan, "--revision", fixture.Seed,
            "--work", fixture.Work, "--output", fixture.Output, "--cache-root", cache);
        Assert.True(result.Success, "[FAIL] cache_save_failure_preserves_valid_current_artifact: " + result.Error);
        Assert.Contains("save-failed", result.Output);
        Assert.True(fixture.Validate().Success);
    }

    [Fact]
    public void adjacent_relocation_preserves_complete_history()
    {
        using var fixture = new InformationTemplateHistoryFixture();
        fixture.SeedPlan();
        Assert.True(fixture.Produce().Success);
        var adjacent = Path.Combine(fixture.Scratch.Path, "relocated report", "information-template-history", fixture.Seed);
        var result = fixture.Command("validate", "--plan", fixture.Plan, "--revision", fixture.Seed,
            "--bundle", fixture.Output, "--output", adjacent);
        Assert.True(result.Success, "[FAIL] adjacent_relocation_preserves_complete_history: " + result.Error);
        Assert.True(fixture.Command("validate", "--plan", fixture.Plan, "--revision", fixture.Seed, "--bundle", adjacent).Success);
        Assert.Equal(1, fixture.Productions);
    }
}
