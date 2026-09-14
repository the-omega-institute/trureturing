using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using FixtureFileSystem = StrataLint.TestSupport.TemporaryFileSystem;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AlignmentPlanUsesPhysicalCasPresenceAndExactBytes(bool identicalCas)
    {
        var fixture = AlignmentPlanFixture();
        var atoms = AtomizerRegistry.Atomize(SyntheticNumberedAtomizer.Id,
            Encoding.UTF8.GetBytes(fixture.Files[RuleFixture.FixtureDigestionSourcePath]),
            DigestionTestSupport.Rules).Claims;
        Assert.Equal(2, atoms.Length);
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        if (identicalCas) WritePhysicalCas(temporary, atoms[0]);
        var environment = AlignmentPlanEnvironment(temporary, fixture);

        var plan = ReadAlignmentPlan(environment, temporary);

        var rows = plan.GetProperty("writes").EnumerateArray().ToArray();
        var casRows = rows.Where(row => row.GetProperty("domain").GetString() == "cas").ToArray();
        Assert.Equal(identicalCas ? 1 : 2, casRows.Length);
        foreach (var atom in identicalCas ? atoms.Skip(1) : atoms)
            AssertAlignmentWrite(plan, DigestionCasStore.RootPath + AtomId(atom), "create",
                null, atom.RawBytes.ToArray());
        foreach (var atom in atoms)
            Assert.Contains(rows, row => row.GetProperty("path").GetString()
                == DirectoryAtomPath(AtomId(atom), "residual-open"));
        Assert.DoesNotContain(rows, row => row.GetProperty("path").GetString()
            == BackfillInventoryLoader.RootPath + "fixture-source/source.toml");
        if (identicalCas)
            Assert.DoesNotContain(casRows, row => row.GetProperty("path").GetString()
                == DigestionCasStore.RootPath + AtomId(atoms[0]));
        var expectedImage = AlignmentPlanImage(temporary, plan);
        var result = environment.AlignDigestionStatus(["--base", "baseline"]);
        Assert.True(result.Success, result.Error);
        Assert.Equal(expectedImage, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        var current = AlignmentCurrentFiles(temporary, fixture.Files);
        var next = AlignmentPlanEnvironment(temporary, fixture, current);
        Assert.Empty(ReadAlignmentPlan(next, temporary).GetProperty("writes").EnumerateArray());
        Assert.True(next.AlignDigestionStatus(["--base", "baseline"]).Success);
        Assert.Equal(expectedImage, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }

    [Theory]
    [InlineData("missing-report", false)]
    [InlineData("missing-report", true)]
    [InlineData("invalid-report", false)]
    [InlineData("invalid-report", true)]
    [InlineData("chain", false)]
    [InlineData("chain", true)]
    [InlineData("final-backfill", false)]
    [InlineData("final-backfill", true)]
    [InlineData("scribe", false)]
    [InlineData("scribe", true)]
    [InlineData("cas-collision", false)]
    [InlineData("cas-collision", true)]
    public void AlignmentPlanFailuresDoNotPublishPersistentChanges(string failure, bool planOnly)
    {
        var fixture = AlignmentPlanFixture();
        if (failure == "final-backfill")
        {
            const string singleClaim = "# Synthetic\n\n**定理 1.1(A)**。claim。\n";
            fixture.Files[RuleFixture.FixtureDigestionSourcePath] = singleClaim;
            fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = singleClaim;
        }
        var atoms = AtomizerRegistry.Atomize(SyntheticNumberedAtomizer.Id,
            Encoding.UTF8.GetBytes(fixture.Files[RuleFixture.FixtureDigestionSourcePath]),
            DigestionTestSupport.Rules).Claims;
        if (failure is "chain" or "final-backfill")
        {
            var document = IngestLedger(SyntheticNumberedAtomizer.Id, atoms[0]);
            if (failure == "chain")
                document = MapOnlyEntry(document, entry => entry with
                {
                    Receipts = entry.Receipts with { ChainAtoms = ["missing-child"] },
                });
            else
                document = document.WithDigestionSources(document.RequireDigestionSources()
                    .Select(source => source with
                    {
                        SourceId = "INVALID",
                        Entries = source.Entries.Select(entry => entry with { SourceId = "INVALID" })
                            .ToImmutableArray(),
                    }).ToImmutableArray());
            InstallProjectedLedger(fixture, document, atoms[0]);
        }
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        if (failure == "cas-collision")
        {
            // The conflict exists only on disk, outside the gateway's captured snapshot.
            var path = Path.Combine(temporary.Path, DigestionCasStore.RootPath + AtomId(atoms[1]));
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllBytes(path, [0, 255, 13, 10]);
        }
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var directories = AlignmentDirectories(temporary);
        var scribe = new FakeScribeEmissionVerifier(failure == "scribe" ? null : VerifiedScribeEmissions.Empty);
        var report = failure == "invalid-report"
            ? LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>())
            : LeanAxiomReport.Create(fixture.Reports);
        var environment = new ProductionCliEnvironment(temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create([]), Snapshot(fixture.Files), Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(failure == "missing-report" ? null : report), scribe);

        var result = environment.AlignDigestionStatus(planOnly
            ? ["--base", "baseline", "--plan"] : ["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.StartsWith("INGEST_INVALID ", result.Error, StringComparison.Ordinal);
        Assert.Contains(failure switch
        {
            "missing-report" => "Lean report source",
            "invalid-report" => "report",
            "chain" => "CHILD_CAS_MISSING",
            "final-backfill" => "SL-016 final ledger is invalid",
            "scribe" => "Scribe emission verification failed",
            _ => "CAS path already contains different bytes",
        }, result.Error, StringComparison.OrdinalIgnoreCase);
        if (failure is "final-backfill" or "scribe" or "cas-collision") Assert.Equal(1, scribe.CallCount);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        Assert.Equal(directories, AlignmentDirectories(temporary));
    }

    [Theory]
    [InlineData("")]
    [InlineData("--plan")]
    [InlineData("--base||--plan")]
    [InlineData("--plan|--base|baseline")]
    [InlineData("--base|baseline|--plan|extra")]
    [InlineData("--base|baseline|--plan|--plan")]
    public void AlignmentPlanRejectsMalformedArgumentsWithoutReadingInputs(string input)
    {
        var arguments = input.Length == 0 ? Array.Empty<string>() : input.Split('|');
        var fixture = AlignmentPlanFixture();
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var directories = AlignmentDirectories(temporary);
        var reads = 0;
        var environment = new ProductionCliEnvironment(temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create([]), Snapshot(fixture.Files), Snapshot(fixture.Baseline),
                currentReader: () => { reads++; return Snapshot(fixture.Files); }),
            new FakeLeanReportSource(null), new FakeScribeEmissionVerifier(null));
        var result = environment.AlignDigestionStatus(arguments);
        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.Contains("USAGE:", result.Error, StringComparison.Ordinal);
        Assert.Equal(0, reads);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        Assert.Equal(directories, AlignmentDirectories(temporary));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AlignmentPlanRetainsProductionScribeSnapshotLifecycle(bool throws)
    {
        var fixture = AlignmentPlanFixture();
        const string producer = "Meta/ReportProducers/scribe-content.json";
        const string registration = """
            {"schema":"report-producer-scope-v1","scripts":[],
             "projects":["tools/StrataLint.Scribe/StrataLint.Scribe.csproj"],"materials":[]}
            """;
        fixture.Files[producer] = registration;
        fixture.Baseline[producer] = registration;
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var directories = AlignmentDirectories(temporary);
        string? snapshotRoot = null;
        var verifier = new ProductionScribeEmissionVerifier((root, _, _, _) =>
        {
            snapshotRoot = root;
            Assert.NotEqual(temporary.Path, root);
            Assert.Equal(fixture.Files[RuleFixture.FixtureDigestionSourcePath],
                FixtureFileSystem.File.ReadAllText(Path.Combine(root, RuleFixture.FixtureDigestionSourcePath)));
            Assert.Equal(2, BackfillInventoryLoader.LoadRoot(root).RequireDigestionEntries().Length);
            if (throws) throw new InvalidOperationException("snapshot validation rejected");
            return VerifiedScribeEmissions.Empty;
        });
        var environment = new ProductionCliEnvironment(temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create([RuleFixture.FixtureDigestionSourcePath]),
                Snapshot(fixture.Files), Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)), verifier);
        var result = environment.AlignDigestionStatus(["--base", "baseline", "--plan"]);
        Assert.True(snapshotRoot is not null, result.Error);
        Assert.False(Directory.Exists(snapshotRoot));
        Assert.Equal(!throws, result.Success);
        if (throws)
        {
            Assert.Empty(result.Output);
            Assert.Contains("snapshot validation rejected", result.Error, StringComparison.Ordinal);
        }
        else Assert.NotEmpty(JsonDocument.Parse(result.Output).RootElement.GetProperty("writes").EnumerateArray());
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        Assert.Equal(directories, AlignmentDirectories(temporary));
    }

    private static RuleFixture AlignmentPlanFixture()
    {
        var fixture = new RuleFixture();
        const string text = "# Synthetic\n\n**定理 1.1(A)**。first。\n\n**定理 1.2(B)**。second。\n";
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = text;
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = text;
        InstallProjectedLedger(fixture, DigestionTestSupport.Document(SyntheticNumberedAtomizer.Id,
            [], "fixture-source", RuleFixture.FixtureDigestionSourcePath, GenreRegistryCheck.Collected([])), null);
        return fixture;
    }

    private static ProductionCliEnvironment AlignmentPlanEnvironment(TemporaryDirectory temporary,
        RuleFixture fixture, IReadOnlyDictionary<string, string>? current = null) =>
        new(temporary.Path, new FakeRepositoryGateway(RawChangeSet.Create([]),
                Snapshot(current ?? fixture.Files), Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

    private static void WritePhysicalCas(TemporaryDirectory temporary, DigestionAtom atom)
    {
        var path = Path.Combine(temporary.Path, DigestionCasStore.RootPath + AtomId(atom));
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllBytes(path, atom.RawBytes.AsSpan());
    }

    private static string[] AlignmentDirectories(TemporaryDirectory temporary) =>
        Directory.EnumerateDirectories(temporary.Path, "*", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(temporary.Path, path)).Order(StringComparer.Ordinal).ToArray();

    private static JsonElement ReadAlignmentPlan(ProductionCliEnvironment environment, TemporaryDirectory temporary)
    {
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var directories = AlignmentDirectories(temporary);
        var result = environment.AlignDigestionStatus(["--base", "baseline", "--plan"]);
        Assert.True(result.Success, result.Error);
        Assert.Empty(result.Error);
        Assert.EndsWith("\n", result.Output, StringComparison.Ordinal);
        using var json = JsonDocument.Parse(result.Output);
        var plan = json.RootElement.Clone();
        Assert.Equal("digestion-alignment-plan-v1", plan.GetProperty("schema").GetString());
        Assert.Equal("baseline", plan.GetProperty("baseline_revision").GetString());
        Assert.False(plan.GetProperty("applied").GetBoolean());
        var validation = plan.GetProperty("validation");
        Assert.Equal("converged", validation.GetProperty("fixed_point").GetString());
        Assert.Contains(validation.GetProperty("scope").GetString(), new[] { "FullScan", "ChangedSet" });
        foreach (var key in new[] { "lean", "scribe", "backfill" })
            Assert.Equal("accepted", validation.GetProperty(key).GetString());
        var diagnostics = plan.GetProperty("diagnostics");
        foreach (var key in new[] { "cross_volume_clearance_gaps", "backfill_observations", "digestion_status_text" })
            Assert.Equal(JsonValueKind.String, diagnostics.GetProperty(key).ValueKind);
        foreach (var key in new[] { "silent_zero_sources", "fallback_sources", "open_genres" })
            Assert.Equal(JsonValueKind.Array, diagnostics.GetProperty(key).ValueKind);
        var repeated = environment.AlignDigestionStatus(["--base", "baseline", "--plan"]);
        Assert.True(repeated.Success, repeated.Error);
        Assert.Equal(result.Output, repeated.Output);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        Assert.Equal(directories, AlignmentDirectories(temporary));
        return plan;
    }

    private static byte[]? AlignmentBytes(JsonElement value)
    {
        if (value.ValueKind == JsonValueKind.Null) return null;
        var bytes = Convert.FromBase64String(value.GetProperty("base64").GetString()!);
        Assert.Equal(bytes.Length, value.GetProperty("byte_length").GetInt32());
        Assert.Equal(Convert.ToHexString(SHA256.HashData(bytes)).ToLowerInvariant(),
            value.GetProperty("sha256").GetString());
        return bytes;
    }

    private static void AssertAlignmentWrite(JsonElement plan, string path, string action,
        byte[]? before, byte[]? after)
    {
        var row = Assert.Single(plan.GetProperty("writes").EnumerateArray(),
            row => row.GetProperty("path").GetString() == path);
        Assert.Equal(action, row.GetProperty("action").GetString());
        Assert.Equal(before, AlignmentBytes(row.GetProperty("before")));
        Assert.Equal(after, AlignmentBytes(row.GetProperty("after")));
    }

    private static string AlignmentPlanImage(TemporaryDirectory temporary, JsonElement plan)
    {
        var files = DirectoryLedgerTestSupport.ReadRepository(temporary).Entries
            .ToDictionary(entry => entry.Path, entry => entry.Bytes.ToArray(), StringComparer.Ordinal);
        var rows = plan.GetProperty("writes").EnumerateArray().ToArray();
        Assert.Equal(rows.Length, rows.Select(row => row.GetProperty("path").GetString()).Distinct().Count());
        var ledgerSeen = false;
        var ranks = new List<(int Rank, string Path)>();
        foreach (var row in rows)
        {
            var path = row.GetProperty("path").GetString()!;
            var before = AlignmentBytes(row.GetProperty("before"));
            var after = AlignmentBytes(row.GetProperty("after"));
            Assert.Equal(files.GetValueOrDefault(path), before);
            Assert.False(before is null && after is null);
            Assert.Equal(before is null ? "create" : after is null ? "delete" : "change",
                row.GetProperty("action").GetString());
            if (row.GetProperty("domain").GetString() == "cas")
            {
                Assert.False(ledgerSeen);
                Assert.StartsWith(DigestionCasStore.RootPath, path, StringComparison.Ordinal);
                Assert.Null(before);
                Assert.NotNull(after);
                Assert.Equal(JsonValueKind.Null, row.GetProperty("durability_order").ValueKind);
            }
            else
            {
                ledgerSeen = true;
                Assert.Equal("ledger", row.GetProperty("domain").GetString());
                Assert.StartsWith(BackfillInventoryLoader.RootPath, path, StringComparison.Ordinal);
                ranks.Add((row.GetProperty("durability_order").GetInt32(), path));
            }
            if (after is null) files.Remove(path);
            else files[path] = after;
        }
        Assert.Equal(ranks.OrderBy(item => item.Rank).ThenBy(item => item.Path, StringComparer.Ordinal), ranks);
        return string.Concat(files.OrderBy(pair => pair.Key, StringComparer.Ordinal)
            .Select(pair => pair.Key + "\0" + Convert.ToBase64String(pair.Value) + "\n"));
    }

    private static Dictionary<string, string> AlignmentCurrentFiles(TemporaryDirectory temporary,
        IReadOnlyDictionary<string, string> original)
    {
        var current = new Dictionary<string, string>(original, StringComparer.Ordinal);
        foreach (var path in current.Keys.Where(BackfillInventoryLoader.IsCanonicalPath).ToArray())
            current.Remove(path);
        return DirectoryLedgerTestSupport.OverlayRepositoryFiles(temporary, current);
    }
}
