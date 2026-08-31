using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.DigestionTestSupport;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed class DagLedgerMathlibReanchorWriterTests
{
    private const string BaseRevision = "base";
    private const string BaseToolchain = "leanprover/lean4:v4.32.0\n";
    private const string CandidateToolchain = "leanprover/lean4:v4.33.0\n";
    private const string ModuleASource = "theorem a : True := by trivial\n";
    private const string ModuleBSource = "theorem b : True := by trivial\n";

    [Fact]
    public void CanonicalProducerReplacesExactlyStatementIdentityDrift()
    {
        using var fixture = CreateFixture(
            ModuleASource,
            ModuleASource,
            candidateAStatement: "compiler-reanchored True");

        var result = DagLedgerMathlibReanchorWriter.Reanchor(
            fixture.RepositoryRoot,
            fixture.Repository,
            fixture.ReportSource,
            ["--base", BaseRevision]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("MATHLIB_REANCHOR replacement_modules=1", result.Output, StringComparison.Ordinal);
        Assert.Contains("AUTHORIZATION incremental_replacement=pass", result.Output, StringComparison.Ordinal);
        Assert.Contains("AUTHORIZATION effective_lean_pins_changed=pass", result.Output, StringComparison.Ordinal);
        Assert.Contains("AUTHORIZATION proposition_source_equivalent=pass failed_modules=0", result.Output, StringComparison.Ordinal);
        Assert.Contains("AUTHORIZATION standard_axiom_closure=pass failed_modules=0", result.Output, StringComparison.Ordinal);
        Assert.Contains("AUTHORIZATION overall=pass", result.Output, StringComparison.Ordinal);

        var persisted = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(fixture.LedgerPath);
        Assert.Equal(2, persisted.Length);
        Assert.Contains(persisted, file => file.Path == EventFor(fixture.CandidateEvents, "A").Path);
        var retainedB = EventFor(fixture.BaseEvents, "B");
        var persistedB = Assert.Single(persisted, file => file.Path == retainedB.Path);
        Assert.True(retainedB.RawBytes.AsSpan().SequenceEqual(persistedB.RawBytes.AsSpan()));
    }

    [Fact]
    public void CanonicalProducerReanchorsCoverageReceiptsWithTheFrozenReplacement()
    {
        using var fixture = CreateFixture(
            ModuleASource,
            ModuleASource,
            candidateAStatement: "compiler-reanchored True",
            includeCoverageReceipt: true);

        var result = DagLedgerMathlibReanchorWriter.Reanchor(
            fixture.RepositoryRoot,
            fixture.Repository,
            fixture.ReportSource,
            ["--base", BaseRevision]);

        Assert.True(result.Success, result.Error);
        var receipt = Assert.Single(Assert.Single(
            BackfillInventoryLoader.LoadRoot(fixture.RepositoryRoot)
                .RequireDigestionEntries()).Receipts.Coverage);
        Assert.Equal(
            BuildCatalogWithEnvironment(
                CandidateToolchain,
                "[package]\nname = \"fixture\"\n",
                Manifest('b'),
                GitOid('e'),
                GitOid('f'),
                [ModuleWithReport("A", ModuleASource, "compiler-reanchored True"),
                    ModuleWithReport("B", ModuleBSource, "True")])
                .ByPath[RepoPathFor("A")].StatementId.Value,
            receipt.TargetStatementId);
    }

    [Fact]
    public void CanonicalProducerConvergesWhenPriorReanchorIsPresentBesideProtectedBase()
    {
        using var fixture = CreateFixture(
            ModuleASource,
            ModuleASource,
            candidateAStatement: "compiler-reanchored True",
            includePriorCandidateAEvent: true);

        var result = DagLedgerMathlibReanchorWriter.Reanchor(
            fixture.RepositoryRoot,
            fixture.Repository,
            fixture.ReportSource,
            ["--base", BaseRevision]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("MATHLIB_REANCHOR replacement_modules=1", result.Output, StringComparison.Ordinal);
        var persisted = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(fixture.LedgerPath);
        Assert.Equal(2, persisted.Length);
        Assert.Contains(persisted, file => file.Path == EventFor(fixture.CandidateEvents, "A").Path);
        Assert.Contains(persisted, file => file.Path == EventFor(fixture.BaseEvents, "B").Path);
        Assert.DoesNotContain(persisted, file => file.Path == EventFor(fixture.BaseEvents, "A").Path);
    }

    [Fact]
    public void PropositionSourceFailureIsReportedWithoutChangingReplacementSet()
    {
        const string changedSource =
            "theorem a : True \u2227 True := by constructor <;> trivial\n";
        using var fixture = CreateFixture(
            ModuleASource,
            changedSource,
            candidateAStatement: "True and True");

        var result = DagLedgerMathlibReanchorWriter.Reanchor(
            fixture.RepositoryRoot,
            fixture.Repository,
            fixture.ReportSource,
            ["--base", BaseRevision]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("MATHLIB_REANCHOR replacement_modules=1", result.Output, StringComparison.Ordinal);
        Assert.Contains("AUTHORIZATION proposition_source_equivalent=fail failed_modules=1", result.Output, StringComparison.Ordinal);
        Assert.Contains("AUTHORIZATION overall=fail", result.Output, StringComparison.Ordinal);
        Assert.Contains(RepoPathFor("A").Value, result.Output, StringComparison.Ordinal);

        var persisted = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(fixture.LedgerPath);
        Assert.Equal(2, persisted.Length);
        Assert.Contains(persisted, file => file.Path == EventFor(fixture.CandidateEvents, "A").Path);
        Assert.Contains(persisted, file => file.Path == EventFor(fixture.BaseEvents, "B").Path);
    }

    [Fact]
    public void CanonicalProducerOrdersReanchoredDependenciesWithinOneAtomicReplacement()
    {
        using var fixture = CreateFixture(
            ModuleASource,
            ModuleASource,
            candidateAStatement: "compiler-reanchored A",
            candidateBStatement: "compiler-reanchored B",
            aImportsB: true,
            includeStableC: true);

        var result = DagLedgerMathlibReanchorWriter.Reanchor(
            fixture.RepositoryRoot,
            fixture.Repository,
            fixture.ReportSource,
            ["--base", BaseRevision]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("MATHLIB_REANCHOR replacement_modules=2", result.Output, StringComparison.Ordinal);
        Assert.Contains("AUTHORIZATION incremental_replacement=pass", result.Output, StringComparison.Ordinal);
        var persisted = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(fixture.LedgerPath);
        Assert.Equal(3, persisted.Length);
        var events = LoadEvents(persisted);
        var eventA = Assert.Single(events, item => item.DescriptorPath == RepoPathFor("A"));
        var eventB = Assert.Single(events, item => item.DescriptorPath == RepoPathFor("B"));
        Assert.Contains(
            eventB.EventHash,
            eventA.Payload.GetProperty("prerequisite_frozen_node_ids")
                .EnumerateArray().Select(static item => item.GetString()));
        Assert.Contains(persisted, file => file.Path == EventFor(fixture.BaseEvents, "C").Path);
    }

    private static ReanchorFixture CreateFixture(
        string baseASource,
        string candidateASource,
        string candidateAStatement,
        string candidateBStatement = "True",
        bool aImportsB = false,
        bool includeStableC = false,
        bool includePriorCandidateAEvent = false,
        bool includeCoverageReceipt = false)
    {
        var baseManifest = Manifest('a');
        var candidateManifest = Manifest('b');
        var baseModules = new[]
        {
            ModuleWithReport("A", baseASource, "True") with
            {
                Imports = aImportsB ? ["B"] : [],
            },
            ModuleWithReport("B", ModuleBSource, "True"),
        }.Concat(includeStableC
            ? [ModuleWithReport("C", "theorem c : True := by trivial\n", "True")]
            : []).ToArray();
        var candidateModules = new[]
        {
            ModuleWithReport("A", candidateASource, candidateAStatement) with
            {
                Imports = aImportsB ? ["B"] : [],
            },
            ModuleWithReport("B", ModuleBSource, candidateBStatement),
        }.Concat(includeStableC
            ? [ModuleWithReport("C", "theorem c : True := by trivial\n", "True")]
            : []).ToArray();
        var baseCatalog = BuildCatalogWithEnvironment(
            BaseToolchain,
            "[package]\nname = \"fixture\"\n",
            baseManifest,
            GitOid('c'),
            GitOid('d'),
            baseModules);
        var candidateCatalog = BuildCatalogWithEnvironment(
            CandidateToolchain,
            "[package]\nname = \"fixture\"\n",
            candidateManifest,
            GitOid('e'),
            GitOid('f'),
            candidateModules);
        var baseEvents = EventFiles(baseCatalog);
        var candidateEvents = EventFiles(candidateCatalog);
        var currentEvents = includePriorCandidateAEvent
            ? baseEvents.Add(EventFor(candidateEvents, "A"))
            : baseEvents;
        var coverageDocument = includeCoverageReceipt
            ? CoverageDocument(baseCatalog.ByPath[RepoPathFor("A")].StatementId.Value)
            : null;
        var baseline = Snapshot(
            BaseToolchain,
            baseManifest,
            baseModules,
            baseEvents,
            coverageDocument);
        var current = Snapshot(
            CandidateToolchain,
            candidateManifest,
            candidateModules,
            currentEvents,
            coverageDocument);
        var changedPaths = new List<(string Path, RawChangeKind Kind)>
        {
            ("lean-toolchain", RawChangeKind.Modified),
            ("lake-manifest.json", RawChangeKind.Modified),
        };
        if (!string.Equals(baseASource, candidateASource, StringComparison.Ordinal))
        {
            changedPaths.Add((PathFor("A"), RawChangeKind.Modified));
        }

        var changes = RawChangeSet.CreateWithKinds(changedPaths);
        var repository = new FakeRepositoryGateway(
            changes,
            current,
            baseline,
            changesForBase: _ => changes);
        var reportSource = new FakeLeanReportSource(Report(candidateModules));
        var temporary = new TemporaryDirectory();
        var ledgerPath = Path.Combine(
            temporary.Path,
            FrozenLedgerChangeClassifier.AcceptedRoot.Replace(
                '/',
                Path.DirectorySeparatorChar));
        WriteLedgerDirectory(ledgerPath, currentEvents);
        if (coverageDocument is not null)
        {
            var files = new Dictionary<string, string>(StringComparer.Ordinal);
            DirectoryLedgerTestSupport.ReplaceWithProjection(files, coverageDocument);
            DirectoryLedgerTestSupport.Write(temporary.Path, files);
        }
        return new ReanchorFixture(
            temporary,
            ledgerPath,
            repository,
            reportSource,
            baseEvents,
            candidateEvents);
    }

    private static RawRepositorySnapshot Snapshot(
        string toolchain,
        string manifest,
        IReadOnlyList<ModuleSpec> modules,
        IEnumerable<RepositoryFile> events,
        BackfillInventoryDocument? coverageDocument)
    {
        var entries = new List<RawRepositoryEntry>
        {
            RawRepositoryEntry.FromText("lean-toolchain", toolchain),
            RawRepositoryEntry.FromText("lakefile.toml", "[package]\nname = \"fixture\"\n"),
            RawRepositoryEntry.FromText("lake-manifest.json", manifest),
        };
        entries.AddRange(modules.Select(module =>
            RawRepositoryEntry.FromText(PathFor(module.Name), module.Source)));
        entries.AddRange(events.Select(file => new RawRepositoryEntry(file.Path.Value, file.RawBytes)));
        if (coverageDocument is not null)
        {
            foreach (var source in coverageDocument.RequireDigestionSources())
            {
                entries.Add(new RawRepositoryEntry(
                    $"{BackfillInventoryLoader.RootPath}{source.SourceId}/source.toml",
                    BackfillInventoryWriter.WriteSourceMetadata(source)));
                foreach (var entry in source.Entries)
                {
                    entries.Add(new RawRepositoryEntry(
                        $"{BackfillInventoryLoader.RootPath}{source.SourceId}/absorbed-closed/"
                            + $"{entry.AtomId}.yaml",
                        BackfillInventoryWriter.WriteAtom(entry)));
                }
            }
        }
        return RawRepositorySnapshot.Create(entries);
    }

    private static BackfillInventoryDocument CoverageDocument(string targetStatementId)
    {
        var bytes = Encoding.UTF8.GetBytes("receipt source\n");
        var atom = new DigestionAtom(
            0,
            bytes.Length,
            ImmutableArray.CreateRange(bytes),
            DigestionFingerprint.Compute(bytes),
            []);
        var gid = "D5/S0/Carrier/A";
        var receipt = new DigestionCoverageReceipt(
            gid,
            atom.Fingerprints.RawSha256,
            targetStatementId);
        var entry = Entry(
            atom,
            atom.Fingerprints.RawSha256["sha256:".Length..],
            AtomizerRegistry.NoAtomizerId,
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Closed,
            [gid],
            new DigestionReceipts([receipt], [], [], [], null));
        return Document(AtomizerRegistry.NoAtomizerId, [entry]);
    }

    private static LeanAxiomReport Report(IEnumerable<ModuleSpec> modules) =>
        LeanAxiomReport.Create(modules.ToDictionary(
            module => PathFor(module.Name),
            module => new LeanFileReport(
                module.Imports.Select(static import => $"D5.S0.Carrier.{import}")
                    .ToImmutableArray(),
                ImmutableArray.Create(new LeanDeclaration(
                    module.Name.ToLowerInvariant(),
                    module.Kind,
                    module.StatementMaterial,
                    module.Axioms)
                {
                    NameKey = $"ns(n0,{Encoding.UTF8.GetByteCount(module.Name)}:{module.Name.ToLowerInvariant()})",
                })),
            StringComparer.Ordinal));

    private static RepositoryFile EventFor(
        IEnumerable<RepositoryFile> events,
        string module)
    {
        var path = RepoPathFor(module);
        var sourcePath = LoadEvents(events).Single(item => item.DescriptorPath == path).SourcePath;
        return events.Single(file => file.Path == sourcePath);
    }

    private static string Manifest(char digit) =>
        $$"""
        {"packages":[{"name":"mathlib","type":"git","rev":"{{new string(digit, 40)}}"}]}
        """ + "\n";

    private sealed record ReanchorFixture(
        TemporaryDirectory Temporary,
        string LedgerPath,
        FakeRepositoryGateway Repository,
        FakeLeanReportSource ReportSource,
        ImmutableArray<RepositoryFile> BaseEvents,
        ImmutableArray<RepositoryFile> CandidateEvents) : IDisposable
    {
        internal string RepositoryRoot => Temporary.Path;

        public void Dispose() => Temporary.Dispose();
    }
}
