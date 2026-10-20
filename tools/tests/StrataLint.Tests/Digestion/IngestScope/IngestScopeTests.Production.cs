using Markdig;
using Markdig.Syntax;
using Markdig.Renderers.Html;
using StrataLint.Engineering;
using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestScopeTests
{
    [Fact]
    public void PathScopedIngestSearchesMetadataWithoutLoadingAnEntireMetadataSnapshot()
    {
        var fixture = Fixture();
        fixture.Files[BetaPath] += Addition;
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([BetaPath]),
            Raw(fixture.Files), Raw(fixture.Baseline));
        var environment = new ProductionCliEnvironment(temporary.Path, gateway, new FakeLeanReportSource(null));

        var result = environment.Ingest(["--source", BetaPath]);

        Assert.True(result.Success, result.Error);
        Assert.Equal(0, gateway.WholeTreeReadCount);
        Assert.DoesNotContain(gateway.ScopedCurrentReads.SelectMany(static scope => scope),
            static path => path.StartsWith(":(glob)", StringComparison.Ordinal)
                && path.EndsWith("/source.toml", StringComparison.Ordinal));
        var after = DirectoryLedgerTestSupport.ReadRepository(temporary);
        Assert.Single(BackfillInventoryLoader.Load(Decode(after)).RequireDigestionSources()
            .Single(static source => source.SourceId == "beta").Entries
            .Where(entry => entry.AtomId == Atom(Addition).Fingerprints.RawSha256[7..]));
        Assert.NotEqual(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }

    [Fact]
    public void ReportFreeIngestReadsSourcesWithoutCoverageOrEngineeringInputs()
    {
        var fixture = Fixture();
        fixture.Files[BetaPath] += Addition;
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create([BetaPath]),
            Raw(fixture.Files),
            Raw(fixture.Baseline));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            gateway,
            new FakeLeanReportSource(null),
            new FakeScribeEmissionVerifier(null));

        var result = environment.Ingest(["--source", "beta"]);

        Assert.True(result.Success, result.Error);
        var reads = gateway.ScopedCurrentReads.SelectMany(static scope => scope).ToArray();
        Assert.DoesNotContain(reads, static path => path == EngineeringProjectSchema.ManifestPath);
        Assert.DoesNotContain(reads, static path => path.StartsWith("D5/", StringComparison.Ordinal));
        Assert.DoesNotContain(reads, static path => path.Contains("BackfillTarget", StringComparison.Ordinal));
    }

    [Theory]
    [InlineData("beta")]
    [InlineData("alpha")]
    [InlineData("all")]
    public void IngestScope_ConflictMarkerPrepassRespectsSelectedSource_ProductionPath(string selector)
    {
        var fixture = Fixture();
        fixture.Files[AlphaPath] += "<<<<<<< HEAD\nconflicted text\n=======\nother text\n>>>>>>> incoming\n";
        fixture.Files[BetaPath] += Addition;
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.ReadRepository(temporary);

        var result = Environment(fixture, temporary).Ingest(
            selector == "all" ? Arguments("alpha", "beta") : Arguments(selector));

        var after = DirectoryLedgerTestSupport.ReadRepository(temporary);
        if (selector == "beta")
        {
            Assert.True(result.Success, result.Error);
            Assert.Equal(Image(before, SourcePrefix("alpha")), Image(after, SourcePrefix("alpha")));
            var beforePaths = before.Entries.Select(static entry => entry.Path).ToHashSet(StringComparer.Ordinal);
            Assert.Equal(Image(before), Image(RawRepositorySnapshot.Create(
                after.Entries.Where(entry => beforePaths.Contains(entry.Path)))));
            var addedId = Atom(Addition).Fingerprints.RawSha256["sha256:".Length..];
            Assert.Equal(new[]
            {
                DigestionCasStore.RootPath + addedId,
                SourcePrefix("beta") + "residual-open/" + addedId + ".yaml",
            }.Order(StringComparer.Ordinal), after.Entries
                .Where(entry => !beforePaths.Contains(entry.Path)).Select(static entry => entry.Path)
                .Order(StringComparer.Ordinal));
        }
        else
        {
            Assert.False(result.Success);
            Assert.Contains("INGEST-CONFLICT-MARKER-001", result.Error, StringComparison.Ordinal);
            Assert.Contains(AlphaPath + ":5", result.Error, StringComparison.Ordinal);
            Assert.Equal(Image(before), Image(after));
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Ingest_UnselectedSourceAtomizerNeverCalledInAnyPass(bool contentKinds)
    {
        var document = Ledger();
        var fixture = RobustFixture(document, document);
        fixture.Files[BetaPath] += Addition;
        var calls = new Dictionary<string, int>(StringComparer.Ordinal)
        {
            ["alpha"] = 0,
            ["beta"] = 0,
        };
        string SourceFor(ReadOnlySpan<byte> bytes) =>
            bytes.SequenceEqual(Encoding.UTF8.GetBytes(AlphaText)) ? "alpha" : "beta";
        TheoryAtomizer atomizer = (bytes) =>
        {
            calls[SourceFor(bytes)]++;
            return GenericAtomizer.Atomize(bytes);
        };
        TheoryAtomizerWithContentKinds contentAtomizer = (bytes, kinds) =>
        {
            calls[SourceFor(bytes)]++;
            return GenericAtomizer.AtomizeWithContentKinds(bytes, kinds);
        };
        var dependencies = contentKinds
            ? new ReportFreeIngestDependencies(
                ContentKindAtomizerResolver: _ => contentAtomizer)
            : new ReportFreeIngestDependencies(AtomizerResolver: _ => atomizer);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);

        var result = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([AlphaPath, BetaPath]),
            dependencies).Ingest(Arguments("beta"));

        Assert.True(result.Success, result.Error);
        Assert.Equal(0, calls["alpha"]);
        Assert.Equal(1, calls["beta"]);
    }

    [Fact]
    public void IngestScope_UnselectedContentWideReplacementPrepassSkipped_ProductionPath()
    {
        var original = Ledger();
        var alpha = original.RequireDigestionSources()[0];
        var alphaText = "# Header\n\n" + AlphaText;
        var bytes = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(alphaText));
        var opaque = DigestionAtom.FromFrozenCas(
            bytes,
            DigestionFingerprint.ComputeOpaque(bytes.AsSpan()));
        var old = DigestionTestSupport.Entry(
            opaque,
            opaque.Fingerprints.RawSha256["sha256:".Length..],
            AtomizerRegistry.GenericId,
            sourceId: "alpha",
            sourcePath: AlphaPath);
        var baseline = original.WithDigestionSources(
        [
            alpha with { Atomizer = AtomizerRegistry.GenericId, Entries = [old] },
            original.RequireDigestionSources()[1],
        ]);
        var current = original.WithDigestionSources(
        [
            alpha with
            {
                Entries =
                [
                    old with
                    {
                        Atomizer = AtomizerRegistry.GenericId,
                        Fingerprints = old.Fingerprints with
                        {
                            NormalizedSha256 = "sha256:" + new string('f', 64),
                        },
                    },
                ],
            },
            original.RequireDigestionSources()[1],
        ]);
        var fixture = RobustFixture(current, baseline, alphaText, BetaText);
        AddCas(fixture.Files, opaque);
        AddCas(fixture.Baseline, opaque);
        fixture.Files[BetaPath] += Addition;
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.ReadRepository(temporary);

        var result = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([AlphaPath, BetaPath])).Ingest(Arguments("beta"));

        Assert.True(result.Success, result.Error);
        var after = DirectoryLedgerTestSupport.ReadRepository(temporary);
        Assert.Equal(Image(before, SourcePrefix("alpha")), Image(after, SourcePrefix("alpha")));
    }

    [Fact]
    public void IngestScope_UnselectedUnchainedClauseParentNotMaterialized_SelectedIs_ProductionPath()
    {
        const string alphaText = "## Claim 10\n\n- Alpha first.\n- Alpha second.\n";
        const string betaText = "## Claim 20\n\n- Beta first.\n- Beta second.\n";
        var alpha = Source("alpha", AlphaPath, alphaText);
        var document = TwoSourceLedger(
            alpha,
            Source("beta", BetaPath, betaText, populated: false));
        var fixture = RobustFixture(document, document, alphaText, betaText);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.ReadRepository(temporary);

        var result = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([AlphaPath, BetaPath])).Ingest(Arguments("beta"));

        Assert.True(result.Success, result.Error);
        var after = DirectoryLedgerTestSupport.ReadRepository(temporary);
        Assert.Equal(Image(before, SourcePrefix("alpha")), Image(after, SourcePrefix("alpha")));
        var sources = BackfillInventoryLoader.Load(Decode(after)).RequireDigestionSources();
        var afterAlpha = sources.Single(static source => source.SourceId == "alpha");
        var afterBeta = sources.Single(static source => source.SourceId == "beta");
        Assert.Empty(Assert.Single(afterAlpha.Entries).Receipts.ChainAtoms);
        var betaParentId = Atom(betaText).Fingerprints.RawSha256["sha256:".Length..];
        var betaParent = Assert.Single(afterBeta.Entries, entry => entry.AtomId == betaParentId);
        Assert.Equal(2, betaParent.Receipts.ChainAtoms.Length);
        Assert.Equal(3, afterBeta.Entries.Length);
    }
    private static readonly Lazy<RawRepositorySnapshot> SourceSelectionInputs = new(() =>
        new GitRepositoryGateway(TestRepositoryLayout.FindRoot()).ReadCurrent([
            "Meta/FILEMAP.toml", ":(glob)Meta/FILEMAP.*.toml",
            ":(glob)Meta/Digestion/backfill/*/source.toml",
            ":(glob)docs/develop/archive/theory/*",
            "docs/develop/theory/GICT.md", "docs/develop/theory/PZG_BEDC.md",
            "docs/develop/theory/CONE_PROGRAM_FORMAL.md", "docs/develop/theory/OBSERVER-QUANTUM.md",
            "docs/develop/theory/QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION.md",
            "docs/develop/theory/ORDERED_SIMPLEX_L2_PROJECTION.md",
        ]));

    [Fact]
    public void SourceDiscoveryIncludesCanonicalRegularInputAndExcludesReaderAndArchiveIdentities()
    {
        var snapshot = DecomposeFixture.Decode(SourceSelectionInputs.Value);
        var empty = BackfillInventoryDocument.Create([], []);
        var registered = DigestionIngestor.RegisterDefaultTheorySources(empty, snapshot)
            .RequireDigestionSources();
        var source = Assert.Single(registered);
        Assert.Equal("docs/develop/theory/ORDERED_SIMPLEX_L2_PROJECTION.md", source.SourcePath);
        Assert.Equal("generic-v1", source.Atomizer);
    }

    [Theory]
    [InlineData("bedc-wm-v0.1")]
    [InlineData("cone-v1")]
    [InlineData("gict-v3.6")]
    [InlineData("interface-philosophy-v4")]
    [InlineData("interface-v1")]
    [InlineData("observer-quantum-v1")]
    [InlineData("periodic-tree-registry")]
    [InlineData("priced-interface-v0.0")]
    [InlineData("pzg-v170")]
    [InlineData("qdo-v1")]
    [InlineData("docs/develop/theory/GICT.md")]
    [InlineData("docs/develop/theory/PZG_BEDC.md")]
    [InlineData("docs/develop/theory/CONE_PROGRAM_FORMAL.md")]
    [InlineData("docs/develop/theory/OBSERVER-QUANTUM.md")]
    [InlineData("docs/develop/theory/QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION.md")]
    [InlineData("docs/develop/archive/theory/GICT.md")]
    public void RetiredIdsArchivesAndReaderReferencesCannotBeSelected(string selector)
    {
        var root = TestRepositoryLayout.FindRoot();
        var repository = new FakeRepositoryGateway(RawChangeSet.Create([]), SourceSelectionInputs.Value, null);
        var reachedWrites = false;
        var result = IngestCommand.RunReportFree(root, repository, ["--source", selector],
            new(BeforeValidation: _ => { reachedWrites = true; throw new InvalidOperationException("unexpected eligible input"); }));
        Assert.False(result.Success);
        Assert.False(reachedWrites);
        Assert.False(SourceDispatchCommand.Run(root, repository, ["--source", selector]).Success);
    }

    [Fact]
    public void CanonicalCurrentGenericSourceReachesProductionIngestPlanning()
    {
        var root = TestRepositoryLayout.FindRoot();
        var reachedPlan = false;
        var result = IngestCommand.RunReportFree(root, new GitRepositoryGateway(root),
            ["--source", "docs/develop/theory/ORDERED_SIMPLEX_L2_PROJECTION.md"],
            new(BeforeValidation: _ => { reachedPlan = true; throw new InvalidOperationException("planned input; stop before writes"); }));
        Assert.True(reachedPlan, result.Error);
        Assert.False(result.Success);
        Assert.Contains("planned input; stop before writes", result.Error);
    }

    [Theory]
    [InlineData("FIB_NATIVE_EXTERIOR_RESPONSE_GAIN_BOUND.md")]
    [InlineData("FIB_NATIVE_JOINT_ENDPOINT_SATURATION_BOUNDARY.md")]
    [InlineData("FIB_NATIVE_ACTUAL_CRITICAL_SOLVABILITY_AND_MICROSCOPIC_DISAPPEARANCE.md")]
    [InlineData("FUTURE_GENERIC_SOURCE.md")]
    [InlineData("future/NESTED_GENERIC_SOURCE.md")]
    [InlineData("INTERFACE_PAPER.md")]
    public void NewCanonicalGenericInputsReachProductionSelectionWithoutMemberRegistration(string relative)
    {
        var path = "docs/develop/theory/" + relative;
        var raw = RawRepositorySnapshot.Create(SourceSelectionInputs.Value.Entries
            .Append(RawRepositoryEntry.FromText(path, AlphaText)));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var manifest = FileMapLoader.LoadSnapshot(snapshot);
        Assert.True(Assert.Single(manifest.Match(path)).DigestionSource);
        Assert.True(DigestionSourceEligibility.IsEligible(snapshot, path));
        var registered = DigestionIngestor.RegisterDefaultTheorySources(
            BackfillInventoryDocument.Create([], []), snapshot).RequireDigestionSources();
        Assert.Contains(registered, source => source.SourcePath == path && source.Atomizer == "generic-v1");
        var reachedPlan = false;
        var result = IngestCommand.RunReportFree(TestRepositoryLayout.FindRoot(),
            new FakeRepositoryGateway(RawChangeSet.Create([path]), raw, null), ["--source", path],
            new(BeforeValidation: _ => { reachedPlan = true; throw new InvalidOperationException("planned new input; stop before writes"); }));
        Assert.True(reachedPlan, result.Error);
        Assert.False(result.Success);
        Assert.Contains("planned new input; stop before writes", result.Error);
    }

    [Fact]
    public void NewArchiveInputsRemainIneligibleForDefaultAndExplicitSelectionBeforeWrites()
    {
        const string path = "docs/develop/archive/theory/FUTURE_GENERIC_SOURCE.md";
        var raw = RawRepositorySnapshot.Create(SourceSelectionInputs.Value.Entries
            .Append(RawRepositoryEntry.FromText(path, AlphaText)));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        Assert.False(DigestionSourceEligibility.IsEligible(snapshot, path));
        Assert.DoesNotContain(DigestionIngestor.RegisterDefaultTheorySources(
            BackfillInventoryDocument.Create([], []), snapshot).RequireDigestionSources(),
            source => source.SourcePath == path);
        var reachedWrites = false;
        var repository = new FakeRepositoryGateway(RawChangeSet.Create([path]), raw, null);
        var result = IngestCommand.RunReportFree(TestRepositoryLayout.FindRoot(), repository, ["--source", path],
            new(BeforeValidation: _ => { reachedWrites = true; throw new InvalidOperationException("unexpected archive selection"); }));
        Assert.False(result.Success);
        Assert.False(reachedWrites);
        Assert.False(SourceDispatchCommand.Run(TestRepositoryLayout.FindRoot(), repository, ["--source", path]).Success);
    }

    [Theory]
    [InlineData("docs/develop/theory/GICT.md")]
    [InlineData("docs/develop/archive/theory/GICT.md")]
    public void ReaderAndArchivePolicyRejectsParserCommandsBeforeWrites(string sourcePath)
    {
        var fixture = new DecomposeFixture();
        var source = Assert.Single(fixture.Document.RequireDigestionSources()) with { SourcePath = sourcePath };
        fixture.Current = RawRepositorySnapshot.Create(fixture.Current.Entries
            .Where(entry => entry.Path != "docs/probe.md"
                && entry.Path != BackfillInventoryLoader.RootPath + "probe/source.toml"
                && !entry.Path.StartsWith("Meta/FILEMAP.", StringComparison.Ordinal))
            .Append(RawRepositoryEntry.FromText(sourcePath, DecomposeFixture.Bold))
            .Append(new RawRepositoryEntry(BackfillInventoryLoader.RootPath + "probe/source.toml",
                BackfillInventoryWriter.WriteSourceMetadata(source)))
            .Concat(SourceSelectionInputs.Value.Entries.Where(entry => entry.Path == FileMapLoader.RelativePath
                || entry.Path.StartsWith("Meta/FILEMAP.", StringComparison.Ordinal))));

        var decompose = DecomposeAtomCommand.Run("synthetic", fixture.Gateway, fixture.Args(), fixture.Apply);
        Assert.False(decompose.Success);
        Assert.Contains("ineligible digestion source", decompose.Error);
        Assert.Equal(0, fixture.Writes);
        var context = AtomContextCommand.Run(fixture.Gateway, ["--atom-id", fixture.Parent.AtomId]);
        Assert.False(context.Success);
        Assert.Contains("ineligible digestion source", context.Error);
        using var temporary = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(temporary.Path, fixture.Current);
        var image = SettleAtomCommandTests.Image(temporary);
        var settle = SettleAtomCommandTests.Run(temporary.Path, fixture.Current,
            "atom_id = \"" + fixture.Parent.AtomId + "\"\njustification = \"prose\"\nprevious_atom_id = \"source-boundary\"\nnext_atom_id = \"source-boundary\"\n");
        Assert.False(settle.Success);
        Assert.Contains("ineligible digestion source", settle.Error);
        Assert.Equal(image, SettleAtomCommandTests.Image(temporary));
    }


    [Theory]
    [InlineData("wm-v1")]
    [InlineData("cone-v1")]
    [InlineData("gict-v1")]
    [InlineData("pzg-v1")]
    [InlineData("observer-v1")]
    [InlineData("periodic-tree-v1")]
    [InlineData("dialect:qdo")]
    [InlineData("dialect:arbitrary")]
    [InlineData("none")]
    [InlineData("unknown")]
    public void UnsupportedFormatsRejectAcrossParserCommandsBeforeWrites(string format)
    {
        var fixture = new DecomposeFixture(atomizer: format);
        var reachedWrite = false;
        var ingest = IngestCommand.RunReportFree("synthetic", fixture.Gateway, ["--source", "probe"],
            new(BeforeValidation: _ => { reachedWrite = true; throw new InvalidOperationException("write boundary"); }));
        Assert.False(ingest.Success);
        Assert.Contains("Unknown atomizer id", ingest.Error);
        Assert.False(reachedWrite);
        var decompose = DecomposeAtomCommand.Run("synthetic", fixture.Gateway, fixture.Args(), fixture.Apply);
        Assert.False(decompose.Success);
        Assert.Contains("Unknown atomizer id", decompose.Error);
        Assert.Equal(0, fixture.Writes);
        var context = AtomContextCommand.Run(fixture.Gateway, ["--atom-id", fixture.Parent.AtomId]);
        Assert.False(context.Success);
        Assert.Contains("ATOMIZER_UNSUPPORTED", context.Error);
        using var temporary = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(temporary.Path, fixture.Current);
        var image = SettleAtomCommandTests.Image(temporary);
        var settle = SettleAtomCommandTests.Run(temporary.Path, fixture.Current,
            "atom_id = \"" + fixture.Parent.AtomId + "\"\njustification = \"prose\"\nprevious_atom_id = \"source-boundary\"\nnext_atom_id = \"source-boundary\"\n");
        Assert.False(settle.Success);
        Assert.Contains("ATOMIZER_UNSUPPORTED", settle.Error);
        Assert.Equal(image, SettleAtomCommandTests.Image(temporary));
    }

    [Fact]
    public void ArchiveMarkdownRetainsResolvableLinksAndReaderAnchorRendering()
    {
        var root = TestRepositoryLayout.FindRoot();
        var archive = Path.Combine(root, "docs/develop/archive/theory");
        var pipeline = new MarkdownPipelineBuilder().UseAdvancedExtensions().Build();
        var relative = 0;
        var fragments = 0;
        var unresolved = 0;
        foreach (var path in Directory.EnumerateFiles(archive, "*.md"))
        {
            var text = File.ReadAllText(path);
            var document = Markdown.Parse(text, pipeline);
            var anchors = document.Descendants<HeadingBlock>().Select(heading => heading.GetAttributes().Id)
                .OfType<string>().ToHashSet(StringComparer.Ordinal);
            foreach (var link in document.Descendants<Markdig.Syntax.Inlines.LinkInline>())
            {
                if (link.Url is not { Length: > 0 } url || Uri.TryCreate(url, UriKind.Absolute, out _)) continue;
                if (url.StartsWith('#'))
                {
                    fragments++;
                    if (!anchors.Contains(Uri.UnescapeDataString(url[1..]))) unresolved++;
                    continue;
                }
                relative++;
                var target = Uri.UnescapeDataString(url.Split('#')[0]);
                var original = Path.GetFullPath(Path.Combine(root, "docs/develop/theory", target));
                var moved = Path.GetFullPath(Path.Combine(archive, target));
                Console.WriteLine($"ARCHIVE_LINK owner={Path.GetFileName(path)} url={url} original_resolves={File.Exists(original)} archive_resolves={File.Exists(moved)}");
                if (File.Exists(original)) Assert.True(File.Exists(moved), url);
            }
            var reader = Path.Combine(root, "docs/develop/theory", Path.GetFileName(path));
            if (new FileInfo(reader).LinkTarget is null) continue;
            Assert.Equal(text, File.ReadAllText(reader));
            Assert.Equal(Markdown.ToHtml(text, pipeline), Markdown.ToHtml(File.ReadAllText(reader), pipeline));
        }
        var incoming = 0;
        var owners = new HashSet<string>(StringComparer.Ordinal);
        var referenced = new HashSet<string>(StringComparer.Ordinal);
        var targets = Directory.EnumerateFiles(archive, "*.md")
            .Select(path => Path.Combine(root, "docs/develop/theory", Path.GetFileName(path)))
            .ToHashSet(StringComparer.Ordinal);
        foreach (var path in Directory.EnumerateFiles(Path.Combine(root, "docs"), "*.md", SearchOption.AllDirectories))
        {
            if (path.StartsWith(archive + Path.DirectorySeparatorChar, StringComparison.Ordinal)
                || new FileInfo(path).LinkTarget is not null) continue;
            foreach (var link in Markdown.Parse(File.ReadAllText(path), pipeline)
                .Descendants<Markdig.Syntax.Inlines.LinkInline>())
            {
                if (link.Url is not { Length: > 0 } url || Uri.TryCreate(url, UriKind.Absolute, out _)) continue;
                var target = Uri.UnescapeDataString(url.Split('#')[0]);
                var reader = Path.GetFullPath(Path.Combine(Path.GetDirectoryName(path)!, target));
                if (!targets.Contains(reader)) continue;
                Assert.NotNull(new FileInfo(reader).LinkTarget);
                Assert.True(File.Exists(reader), url);
                incoming++;
                owners.Add(path);
                referenced.Add(reader);
            }
        }
        Assert.Equal(26, incoming);
        Assert.Equal(8, owners.Count);
        Assert.Equal(5, referenced.Count);
        Console.WriteLine($"ARCHIVE_MARKDOWN relative_links={relative} fragment_links={fragments} unresolved_fragments={unresolved} incoming_links={incoming} owners={owners.Count} reader_targets={referenced.Count}");
    }

}
