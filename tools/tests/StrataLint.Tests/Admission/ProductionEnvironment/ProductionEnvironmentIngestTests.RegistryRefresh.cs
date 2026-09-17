using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void RegistryRefreshPublishesExactPlanAndOnlyAppliesSelectedExistingSource()
    {
        var fixture = RegistryRefreshFixture();
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var before = BackfillInventoryLoader.LoadRoot(temporary.Path);
        var environment = RegistryRefreshEnvironment(temporary.Path, fixture);
        var plan = environment.AlignDigestionStatus(
            ["--base", "baseline", "--refresh-source", "fixture-source", "--plan"]);
        Assert.True(plan.Success, plan.Error);
        Assert.Equal(RegistryBytes(before),
            RegistryBytes(BackfillInventoryLoader.LoadRoot(temporary.Path)));
        using var json = JsonDocument.Parse(plan.Output);
        var write = Assert.Single(json.RootElement.GetProperty("writes").EnumerateArray());
        Assert.Equal("Meta/Digestion/backfill/fixture-source/source.toml", write.GetProperty("path").GetString());
        var expected = Convert.FromBase64String(write.GetProperty("after_base64").GetString()!);
        var applied = environment.AlignDigestionStatus(
            ["--base", "baseline", "--refresh-source", RuleFixture.FixtureDigestionSourcePath,
                "--apply", json.RootElement.GetProperty("plan_hash").GetString()!]);
        Assert.True(applied.Success, applied.Error);
        var after = BackfillInventoryLoader.LoadRoot(temporary.Path);
        var source = Assert.Single(after.RequireDigestionSources());
        Assert.Equal(["更正命题"], source.GenreRegistryCheck.UnregisteredGenres.ToArray());
        Assert.Equal(GenreRegistryCheckKind.Collected, source.GenreRegistryCheck.Kind);
        Assert.Equal(expected, BackfillInventoryWriter.WriteSourceMetadata(source).ToArray());
        Assert.Equal(BackfillInventoryWriter.WriteAtom(Assert.Single(before.RequireDigestionEntries())).ToArray(),
            BackfillInventoryWriter.WriteAtom(Assert.Single(after.RequireDigestionEntries())).ToArray());
        using var appliedJson = JsonDocument.Parse(applied.Output);
        Assert.Equal(json.RootElement.GetProperty("writes").GetRawText(),
            appliedJson.RootElement.GetProperty("writes").GetRawText());
        fixture.Files["Meta/Digestion/backfill/fixture-source/source.toml"] = Encoding.UTF8.GetString(expected);
        var noOp = RegistryRefreshEnvironment(temporary.Path, fixture).AlignDigestionStatus(
            ["--base", "baseline", "--refresh-source", "fixture-source", "--plan"]);
        Assert.True(noOp.Success, noOp.Error);
        using var noOpJson = JsonDocument.Parse(noOp.Output);
        Assert.Empty(noOpJson.RootElement.GetProperty("writes").EnumerateArray());
    }

    [Fact]
    public void RegistryRefreshRejectsAmbiguousSourcePathWithoutWriting()
    {
        var fixture = RegistryRefreshFixture();
        var document = BackfillInventoryLoader.Load(Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(Snapshot(fixture.Files))).Snapshot);
        var source = Assert.Single(document.RequireDigestionSources());
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Files,
            document.WithDigestionSources([source, source with { SourceId = "second-source", Entries = [] }]));
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var before = RegistryBytes(BackfillInventoryLoader.LoadRoot(temporary.Path));
        var result = RegistryRefreshEnvironment(temporary.Path, fixture).AlignDigestionStatus(
            ["--base", "baseline", "--refresh-source", source.SourcePath, "--plan"]);
        Assert.False(result.Success);
        Assert.Contains("exactly one existing source", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, RegistryBytes(BackfillInventoryLoader.LoadRoot(temporary.Path)));
    }

    [Fact]
    public void RegistryRefreshRejectsPlanAfterUnrelatedInputChanges()
    {
        var fixture = RegistryRefreshFixture();
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var before = RegistryBytes(BackfillInventoryLoader.LoadRoot(temporary.Path));
        var plan = RegistryRefreshEnvironment(temporary.Path, fixture).AlignDigestionStatus(
            ["--base", "baseline", "--refresh-source", "fixture-source", "--plan"]);
        Assert.True(plan.Success, plan.Error);
        using var json = JsonDocument.Parse(plan.Output);
        fixture.Files["docs/develop/theory/unregistered.md"] += "unrelated edit\n";
        var applied = RegistryRefreshEnvironment(temporary.Path, fixture).AlignDigestionStatus(
            ["--base", "baseline", "--refresh-source", "fixture-source", "--apply",
                json.RootElement.GetProperty("plan_hash").GetString()!]);
        Assert.False(applied.Success);
        Assert.Contains("published plan does not match", applied.Error, StringComparison.Ordinal);
        Assert.Equal(before, RegistryBytes(BackfillInventoryLoader.LoadRoot(temporary.Path)));
    }

    [Theory]
    [InlineData("missing-source")]
    [InlineData("docs/develop/theory/unregistered.md")]
    [InlineData("")]
    public void RegistryRefreshRejectsInvalidSelectorWithoutWriting(string selector)
    {
        var fixture = RegistryRefreshFixture();
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var before = RegistryBytes(BackfillInventoryLoader.LoadRoot(temporary.Path));
        var result = RegistryRefreshEnvironment(temporary.Path, fixture).AlignDigestionStatus(
            ["--base", "baseline", "--refresh-source", selector, "--plan"]);
        Assert.False(result.Success);
        Assert.Contains("REGISTRY_REFRESH_INVALID", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, RegistryBytes(BackfillInventoryLoader.LoadRoot(temporary.Path)));
    }

    [Theory]
    [InlineData("report")]
    [InlineData("scribe")]
    [InlineData("source")]
    [InlineData("cas")]
    [InlineData("stale")]
    [InlineData("plan")]
    public void RegistryRefreshFailuresLeaveLedgerUnchanged(string failure)
    {
        var fixture = RegistryRefreshFixture();
        if (failure == "source") fixture.Files.Remove(RuleFixture.FixtureDigestionSourcePath);
        if (failure == "cas")
            fixture.Files[fixture.Files.Keys.Single(path => path.StartsWith(DigestionCasStore.RootPath, StringComparison.Ordinal))] = "corrupt";
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var before = RegistryBytes(BackfillInventoryLoader.LoadRoot(temporary.Path));
        var reads = 0;
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), Snapshot(fixture.Files), Snapshot(fixture.Baseline),
            currentReader: () =>
            {
                if (++reads > 1 && failure == "stale") fixture.Files["tools/stale-input.cs"] = "changed";
                return Snapshot(fixture.Files);
            });
        var environment = new ProductionCliEnvironment(temporary.Path, gateway,
            new FakeLeanReportSource(failure == "report" ? null : LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(failure == "scribe" ? null : VerifiedScribeEmissions.Empty));
        var result = environment.AlignDigestionStatus(failure == "plan"
            ? ["--base", "baseline", "--refresh-source", "fixture-source", "--apply", new string('0', 64)]
            : ["--base", "baseline", "--refresh-source", "fixture-source", "--plan"]);
        Assert.False(result.Success);
        Assert.Contains(failure switch
        {
            "report" => "Lean report source",
            "scribe" => "Scribe emission verification failed",
            "source" => "source path is dangling",
            "stale" => "inputs changed during validation",
            "plan" => "published plan does not match",
            _ => "cas",
        }, result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Equal(before, RegistryBytes(BackfillInventoryLoader.LoadRoot(temporary.Path)));
    }

    [Theory]
    [InlineData("selected-source")]
    [InlineData("atomizer-data")]
    [InlineData("added-input")]
    [InlineData("removed-input")]
    public void RegistryRefreshRejectsInputChangedAfterSnapshotCheckBeforeWriter(string mutation)
    {
        var fixture = RegistryRefreshFixture();
        fixture.Files[TheoryAtomizerDataLoader.DataPath] = Encoding.UTF8.GetString(DigestionTestSupport.RulesBytes);
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var sourcePath = Path.Combine(temporary.Path, RuleFixture.FixtureDigestionSourcePath);
        Directory.CreateDirectory(Path.GetDirectoryName(sourcePath)!);
        File.WriteAllText(sourcePath, fixture.Files[RuleFixture.FixtureDigestionSourcePath]);
        string[] LedgerFiles() => Directory.EnumerateFiles(
                Path.Combine(temporary.Path, BackfillInventoryLoader.RootPath), "*", SearchOption.AllDirectories)
            .Order(StringComparer.Ordinal)
            .Select(path => Path.GetRelativePath(temporary.Path, path) + ":" + Convert.ToBase64String(File.ReadAllBytes(path)))
            .ToArray();
        var before = LedgerFiles();
        var plan = RegistryRefreshEnvironment(temporary.Path, fixture).AlignDigestionStatus(
            ["--base", "baseline", "--refresh-source", "fixture-source", "--plan"]);
        Assert.True(plan.Success, plan.Error);
        using var json = JsonDocument.Parse(plan.Output);
        Assert.Single(json.RootElement.GetProperty("writes").EnumerateArray());
        var baselineReads = 0;
        var injected = false;
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), null, null,
            currentReader: () => Snapshot(fixture.Files),
            revisionReader: _ =>
            {
                // The second baseline read follows the successful current-snapshot comparison.
                // Change live input here, without changing either snapshot already compared.
                if (++baselineReads == 2)
                {
                    injected = true;
                    switch (mutation)
                    {
                        case "selected-source":
                            fixture.Files[RuleFixture.FixtureDigestionSourcePath] += "\nconcurrent edit\n";
                            File.WriteAllText(sourcePath, fixture.Files[RuleFixture.FixtureDigestionSourcePath]);
                            break;
                        case "atomizer-data": fixture.Files[TheoryAtomizerDataLoader.DataPath] += "\n# concurrent edit\n"; break;
                        case "added-input": fixture.Files["tools/concurrent-input.cs"] = "changed"; break;
                        case "removed-input": fixture.Files.Remove("docs/develop/theory/unregistered.md"); break;
                    }
                }
                return Snapshot(fixture.Baseline);
            });
        var environment = new ProductionCliEnvironment(temporary.Path, gateway,
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));
        var result = environment.AlignDigestionStatus(
            ["--base", "baseline", "--refresh-source", "fixture-source", "--apply",
                json.RootElement.GetProperty("plan_hash").GetString()!]);
        Assert.True(injected);
        var unchanged = before.SequenceEqual(LedgerFiles());
        Assert.True(!result.Success && unchanged,
            $"mutation={mutation}; applied_success={result.Success}; ledger_unchanged={unchanged}; error={result.Error}");
        Assert.Contains("inputs changed", result.Error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("report", false)]
    [InlineData("report", true)]
    [InlineData("baseline", false)]
    [InlineData("baseline", true)]
    public void RegistryRefreshRejectsLateCapturedInputWithoutLedgerWrites(string input, bool apply)
    {
        var fixture = RegistryRefreshFixture();
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        string[] Files() => Directory.EnumerateFiles(temporary.Path, "*", SearchOption.AllDirectories)
            .Order(StringComparer.Ordinal)
            .Select(path => Path.GetRelativePath(temporary.Path, path) + ":" + Convert.ToBase64String(File.ReadAllBytes(path)))
            .ToArray();
        string[] Directories() => Directory.GetDirectories(temporary.Path, "*", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(temporary.Path, path)).Order(StringComparer.Ordinal).ToArray();
        var beforeFiles = Files();
        var beforeDirectories = Directories();
        var plan = RegistryRefreshEnvironment(temporary.Path, fixture).AlignDigestionStatus(
            ["--base", "baseline", "--refresh-source", "fixture-source", "--plan"]);
        Assert.True(plan.Success, plan.Error);
        using var json = JsonDocument.Parse(plan.Output);
        Assert.Single(json.RootElement.GetProperty("writes").EnumerateArray());
        var initialReport = LeanAxiomReport.Create(fixture.Reports);
        var changedReports = fixture.Reports.ToDictionary(pair => pair.Key, pair => pair.Value);
        changedReports[RuleFixture.RingPath] = changedReports[RuleFixture.RingPath] with { Imports = ["ChangedImport"] };
        var lateReport = LeanAxiomReport.Create(changedReports);
        var baselineReads = 0;
        var injected = false;
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), null, null,
            currentReader: () => Snapshot(fixture.Files),
            revisionReader: _ =>
            {
                var captured = Snapshot(fixture.Baseline);
                // The second baseline read finishes the earlier snapshot comparison.
                // Return that captured value, then expose a changed input to the final guard.
                if (++baselineReads == 2)
                {
                    injected = true;
                    if (input == "baseline") fixture.Baseline["tools/late-baseline.cs"] = "changed baseline input";
                }
                return captured;
            });
        var environment = new ProductionCliEnvironment(temporary.Path, gateway,
            new RegistryRefreshReportSource(() => input == "report" && injected ? lateReport : initialReport),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));
        var result = environment.AlignDigestionStatus(apply
            ? ["--base", "baseline", "--refresh-source", "fixture-source", "--apply",
                json.RootElement.GetProperty("plan_hash").GetString()!]
            : ["--base", "baseline", "--refresh-source", "fixture-source", "--plan"]);
        Assert.True(injected);
        var unchanged = beforeFiles.SequenceEqual(Files());
        var noTemporaryDirectories = beforeDirectories.SequenceEqual(Directories());
        Assert.True(!result.Success && unchanged && noTemporaryDirectories,
            $"input={input}; apply={apply}; accepted={result.Success}; ledger_unchanged={unchanged}; "
            + $"directories_unchanged={noTemporaryDirectories}; error={result.Error}");
        Assert.Contains("inputs changed before publication", result.Error, StringComparison.Ordinal);
        Assert.Empty(result.Output);
    }

    private sealed class RegistryRefreshReportSource(Func<LeanAxiomReport> read) : ILeanReportSource
    {
        public LeanAxiomReport Load(RepositorySnapshot snapshot) => read();
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void RegistryRefreshWriterInputPreconditionRejectsBeforeAnyCommit(bool noOp)
    {
        using var temporary = new TemporaryDirectory();
        var path = $"{BackfillInventoryLoader.RootPath}fixture-source/source.toml";
        var current = RawRepositorySnapshot.Create([RawRepositoryEntry.FromText(path, "original\n")]);
        var fullPath = Path.Combine(temporary.Path, path);
        Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
        File.WriteAllText(fullPath, "original\n");
        var commits = 0;
        var exception = Assert.Throws<InvalidOperationException>(() => IngestCommand.ApplyLedgerUpdatesAtomically(
            temporary.Path, current,
            noOp ? [] : [new IngestCommand.LedgerUpdate(path, [.. Encoding.UTF8.GetBytes("replacement\n")])],
            commit: (_, _) => commits++,
            requireInputsUnchanged: () => throw new InvalidOperationException("changed input")));
        Assert.Equal("changed input", exception.Message);
        Assert.Equal(0, commits);
        Assert.Equal("original\n", File.ReadAllText(fullPath));
        Assert.Equal([fullPath], Directory.GetFiles(temporary.Path, "*", SearchOption.AllDirectories));
    }

    private static byte[] RegistryBytes(BackfillInventoryDocument document) =>
        document.RequireDigestionSources().SelectMany(source => BackfillInventoryWriter.WriteSourceMetadata(source))
            .Concat(document.RequireDigestionEntries().SelectMany(entry => BackfillInventoryWriter.WriteAtom(entry))).ToArray();

    private static RuleFixture RegistryRefreshFixture()
    {
        var fixture = new RuleFixture();
        const string atomizer = "dialect:qdo";
        const string source = "# QDO\n\n## 更正命题 40.2\n\nopen。\n";
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = source;
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = source;
        var atom = Assert.Single(AtomizerRegistry.Atomize(atomizer, Encoding.UTF8.GetBytes(source), DigestionTestSupport.Rules).Claims);
        InstallDirectoryLedger(fixture, atomizer, atom);
        fixture.Files["docs/develop/theory/unregistered.md"] = "# New\n\n**定理 1.1**。new。\n";
        return fixture;
    }

    private static ProductionCliEnvironment RegistryRefreshEnvironment(string root, RuleFixture fixture) =>
        new(root, new FakeRepositoryGateway(RawChangeSet.Create([]), Snapshot(fixture.Files), Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));
}
