using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.SettleAtomCommandTests;

namespace StrataLint.Tests;

public sealed class RetireSourcesCommandTests
{
    private const string Source = "docs/develop/theory/RetirementFixture.md";
    private const string Archive = "docs/develop/archive/theory/RetirementFixture.md";

    [Theory]
    [InlineData("archive")]
    [InlineData("delete")]
    public void PreviewDoesNotWriteAndCommitRemovesOnlyTheSelectedIntakeUnit(string mode)
    {
        using var directory = new TemporaryDirectory();
        var raw = Fixture();
        WriteFiles(directory.Path, raw);
        var report = new FakeLeanReportSource(null);
        var before = Image(directory);
        var gateway = Gateway(directory);
        var preview = RetireSourcesCommand.Run(directory.Path, gateway, report, Args(mode));
        Assert.True(preview.Success, preview.Error);
        Assert.StartsWith("RETIRE_PREVIEW", preview.Output, StringComparison.Ordinal);
        Assert.Equal(before, Image(directory));
        var result = RetireSourcesCommand.Run(directory.Path, gateway, report, Args(mode, write: true));
        Assert.True(result.Success, result.Error);
        Assert.StartsWith("RETIRE_WRITTEN", result.Output, StringComparison.Ordinal);
        var after = ReadFiles(directory);
        Assert.DoesNotContain(after.Entries, entry => entry.Path == Source
            || entry.Path.StartsWith(BackfillInventoryLoader.RootPath + "source/", StringComparison.Ordinal));
        foreach (var original in raw.Entries.Where(entry => entry.Path != Source
                     && !entry.Path.StartsWith(BackfillInventoryLoader.RootPath + "source/", StringComparison.Ordinal)))
            Assert.Equal(original.Bytes.ToArray(), after.Entries.Single(entry => entry.Path == original.Path).Bytes.ToArray());
        if (mode == "archive")
            Assert.Equal(raw.Entries.Single(entry => entry.Path == Source).Bytes.ToArray(),
                after.Entries.Single(entry => entry.Path == Archive).Bytes.ToArray());
        else
            Assert.DoesNotContain(after.Entries, entry => entry.Path == Archive);
        Assert.Equal(0, report.CallCount);
        Assert.Equal(0, gateway.WholeTreeReadCount);
        Assert.Empty(gateway.ReadRevisionCalls);
    }

    [Theory]
    [InlineData("open")]
    [InlineData("forged-terminal")]
    [InlineData("cas")]
    [InlineData("new-claim")]
    [InlineData("chain")]
    [InlineData("archive-collision")]
    [InlineData("foreign-chain")]
    [InlineData("shared-atom")]
    [InlineData("foreign-context")]
    [InlineData("incoming-link")]
    [InlineData("encoded-incoming-link")]
    [InlineData("root-incoming-link")]
    [InlineData("utility-atom")]
    public void IncompleteOrReferencedInputRejectsWithoutChangingAnyByte(string defect)
    {
        using var directory = new TemporaryDirectory();
        var raw = Fixture(terminal: defect != "open");
        var atom = raw.Entries.First(entry => entry.Path.EndsWith(".yaml", StringComparison.Ordinal));
        var id = Path.GetFileNameWithoutExtension(atom.Path);
        switch (defect)
        {
            case "forged-terminal":
                var content = Encoding.UTF8.GetString(atom.Bytes.AsSpan());
                var receiptStart = content.IndexOf("  nonpropositional:", StringComparison.Ordinal);
                Assert.True(receiptStart >= 0);
                raw = Replace(raw, atom.Path, content[..receiptStart]);
                break;
            case "cas": raw = Replace(raw, DigestionCasStore.RootPath + id, "corrupt"); break;
            case "new-claim": raw = Replace(raw, Source, "## New\n\nUnsettled claim.\n"); break;
            case "chain":
                raw = Replace(raw, atom.Path, Encoding.UTF8.GetString(atom.Bytes.AsSpan())
                    + "  chain_atoms:\n    - " + new string('f', 64) + "\n");
                break;
            case "archive-collision": raw = Add(raw, Archive, "existing archive"); break;
            case "foreign-chain":
                raw = Add(raw, BackfillInventoryLoader.RootPath + "foreign/residual-open/" + new string('f', 64) + ".yaml",
                    "receipts:\n  chain_atoms:\n    - " + id + "\n");
                break;
            case "shared-atom":
                raw = Add(raw, BackfillInventoryLoader.RootPath + "foreign/residual-open/" + id + ".yaml", "receipts: null\n");
                break;
            case "foreign-context":
                raw = Add(raw, BackfillInventoryLoader.RootPath + "foreign/context/neighbor.toml", "neighbor = '" + id + "'\n");
                break;
            case "incoming-link": raw = Add(raw, "docs/consumer.md", "[theory](develop/theory/RetirementFixture.md#note)"); break;
            case "encoded-incoming-link": raw = Add(raw, "docs/consumer.md", "[theory](develop/theory/Retirement%46ixture.md#note)"); break;
            case "root-incoming-link": raw = Add(raw, "CURRENT.md", "[theory](docs/develop/theory/Retirement%46ixture.md#note)"); break;
            case "utility-atom": raw = Add(raw, "D5/Consumer.lean", "-- Utility: checker; basis=refutes=atom:" + id + "\n"); break;
        }
        WriteFiles(directory.Path, raw);
        var before = Image(directory);
        var result = RetireSourcesCommand.Run(directory.Path, Gateway(directory), new FakeLeanReportSource(null), Args("archive", true));
        Assert.False(result.Success, defect);
        if (defect == "forged-terminal") Assert.Contains(id, result.Error, StringComparison.Ordinal);
        if (defect.EndsWith("incoming-link", StringComparison.Ordinal)) Assert.Contains("SOURCE_REFERENCED", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, Image(directory));
    }

    [Fact]
    public void FailedSecondPublicationRestoresTheFirstArchiveAndEveryOriginal()
    {
        using var directory = new TemporaryDirectory();
        var raw = BatchFixture();
        WriteFiles(directory.Path, raw);
        var before = Image(directory);
        var publications = 0;
        var result = RetireSourcesCommand.Run(directory.Path, Gateway(directory), new FakeLeanReportSource(null),
            ["--source", "source", "--source", "second", "--mode", "archive", "--write"],
            commit: (temporary, destination) =>
            {
                publications++;
                if (publications == 2)
                {
                    Assert.True(File.Exists(Path.Combine(directory.Path, Archive)));
                    throw new IOException("injected second archive publication failure");
                }
                File.Move(temporary, destination);
            });
        Assert.False(result.Success);
        Assert.Equal(2, publications);
        Assert.Contains("injected", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, Image(directory));
    }

    [Fact]
    public void ConcurrentArchiveCreationIsPreservedWhenPublicationFails()
    {
        using var directory = new TemporaryDirectory();
        var raw = Fixture();
        WriteFiles(directory.Path, raw);
        var result = RetireSourcesCommand.Run(directory.Path, Gateway(directory), new FakeLeanReportSource(null), Args("archive", true),
            beforeArchivePublication: target => File.WriteAllText(target, "concurrent archive"));
        Assert.False(result.Success);
        var after = ReadFiles(directory);
        Assert.Equal("concurrent archive", Encoding.UTF8.GetString(after.Entries.Single(entry => entry.Path == Archive).Bytes.AsSpan()));
        foreach (var original in raw.Entries)
            Assert.Equal(original.Bytes.ToArray(), after.Entries.Single(entry => entry.Path == original.Path).Bytes.ToArray());
        Assert.Equal(raw.Entries.Length + 1, after.Entries.Length);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void InputsAndReferencesAreRevalidatedAfterArchivePublication(bool newReference)
    {
        using var directory = new TemporaryDirectory();
        var raw = Fixture();
        WriteFiles(directory.Path, raw);
        var result = RetireSourcesCommand.Run(directory.Path, Gateway(directory), new FakeLeanReportSource(null), Args("archive", true),
            beforeArchivePublication: _ =>
            {
                if (newReference) File.WriteAllText(Path.Combine(directory.Path, "docs/consumer.md"), "[theory](develop/theory/RetirementFixture.md)");
                else File.AppendAllText(Path.Combine(directory.Path, Source), "\nNew claim.\n");
            });
        Assert.False(result.Success);
        Assert.DoesNotContain(ReadFiles(directory).Entries, entry => entry.Path == Archive);
        foreach (var original in raw.Entries)
            Assert.Equal(original.Path == Source && !newReference
                    ? original.Bytes.ToArray().Concat(Encoding.UTF8.GetBytes("\nNew claim.\n")).ToArray() : original.Bytes.ToArray(),
                ReadFiles(directory).Entries.Single(entry => entry.Path == original.Path).Bytes.ToArray());
        if (newReference) Assert.True(File.Exists(Path.Combine(directory.Path, "docs/consumer.md")));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DeduplicatedSourceWithoutOwnedAtomsStillRequiresCompleteCurrentClaims(bool newClaim)
    {
        using var directory = new TemporaryDirectory();
        const string emptySource = "docs/develop/theory/EmptyOwnerFixture.md";
        var raw = Fixture();
        var owner = raw.Entries.Single(entry => entry.Path == BackfillInventoryLoader.RootPath + "source/source.toml");
        raw = Add(raw, BackfillInventoryLoader.RootPath + "empty/source.toml", Encoding.UTF8.GetString(owner.Bytes.AsSpan())
            .Replace("\"source\"", "\"empty\"", StringComparison.Ordinal).Replace(Source, emptySource, StringComparison.Ordinal));
        raw = Add(raw, emptySource, AtomContextFixture.ThreeClaims + (newClaim ? "\n## New\n\nUnrecorded claim.\n" : string.Empty));
        WriteFiles(directory.Path, WithPolicy(raw, [Source, emptySource]));
        var before = Image(directory);
        var result = RetireSourcesCommand.Run(directory.Path, Gateway(directory), new FakeLeanReportSource(null),
            ["--source", "empty", "--mode", "archive", "--write"]);
        if (newClaim)
        {
            Assert.False(result.Success);
            Assert.Contains("SOURCE_HAS_RESIDUAL", result.Error, StringComparison.Ordinal);
            Assert.Equal(before, Image(directory));
        }
        else
        {
            Assert.True(result.Success, result.Error);
            var after = ReadFiles(directory);
            Assert.DoesNotContain(after.Entries, entry => entry.Path == emptySource
                || entry.Path.StartsWith(BackfillInventoryLoader.RootPath + "empty/", StringComparison.Ordinal));
            Assert.Contains(after.Entries, entry => entry.Path == Source);
        }
    }

    [Fact]
    public void BatchArchivePreservesLinksBetweenSelectedSources()
    {
        using var directory = new TemporaryDirectory();
        var raw = BatchFixture(linkSources: true);
        WriteFiles(directory.Path, raw);
        var result = RetireSourcesCommand.Run(directory.Path, Gateway(directory), new FakeLeanReportSource(null),
            ["--source", "source", "--source", "second", "--mode", "archive", "--write"]);
        Assert.True(result.Success, result.Error);
        var after = ReadFiles(directory);
        Assert.Contains("[other](SecondFixture.md#section)",
            Encoding.UTF8.GetString(after.Entries.Single(entry => entry.Path == Archive).Bytes.AsSpan()), StringComparison.Ordinal);
        Assert.Contains("[other](RetirementFixture.md#section)",
            Encoding.UTF8.GetString(after.Entries.Single(entry => entry.Path == "docs/develop/archive/theory/SecondFixture.md").Bytes.AsSpan()), StringComparison.Ordinal);
        Assert.DoesNotContain(after.Entries, entry => entry.Path.StartsWith(BackfillInventoryLoader.RootPath + "source/", StringComparison.Ordinal)
            || entry.Path.StartsWith(BackfillInventoryLoader.RootPath + "second/", StringComparison.Ordinal));
    }

    [Fact]
    public void NewlyCreatedReverseReferenceAbortsBeforeAnyRemoval()
    {
        using var directory = new TemporaryDirectory();
        var raw = Fixture();
        WriteFiles(directory.Path, raw);
        var result = RetireSourcesCommand.Run(directory.Path, Gateway(directory), new FakeLeanReportSource(null), Args("delete", true),
            beforeCommit: () => TemporaryFileSystem.File.WriteAllText(Path.Combine(directory.Path, "docs/consumer.md"), Source));
        Assert.False(result.Success);
        var after = ReadFiles(directory);
        foreach (var original in raw.Entries)
            Assert.Equal(original.Bytes.ToArray(), after.Entries.Single(entry => entry.Path == original.Path).Bytes.ToArray());
    }

    [Theory]
    [InlineData("../bad")]
    [InlineData("missing")]
    public void InvalidSourceNeverWrites(string selector)
    {
        using var directory = new TemporaryDirectory();
        WriteFiles(directory.Path, Fixture());
        var before = Image(directory);
        var result = RetireSourcesCommand.Run(directory.Path, Gateway(directory), new FakeLeanReportSource(null),
            ["--source", selector, "--mode", "delete", "--write"]);
        Assert.False(result.Success);
        Assert.Equal(before, Image(directory));
    }

    [Fact]
    public void MissingArgumentsCannotTriggerRetirement()
    {
        using var directory = new TemporaryDirectory();
        var result = RetireSourcesCommand.Run(directory.Path, Gateway(directory), new FakeLeanReportSource(null), []);
        Assert.False(result.Success);
        Assert.Contains("USAGE:", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ArchiveRelocatesMarkdownLinksImagesAndReferenceDefinitions()
    {
        using var directory = new TemporaryDirectory();
        WriteFiles(directory.Path, Fixture(text: AtomContextFixture.ThreeClaims.Replace("Before.",
            "Before $[p](t)$ [spec](../spec/guide.md#bound), ![image](../images/a.png) and [ref][target].\n\n[target]: ../spec/ref.md#part\n\n[\n[p](t)\n]\n", StringComparison.Ordinal)));
        var result = RetireSourcesCommand.Run(directory.Path, Gateway(directory), new FakeLeanReportSource(null), Args("archive", true));
        Assert.True(result.Success, result.Error);
        var archived = Encoding.UTF8.GetString(ReadFiles(directory).Entries.Single(entry => entry.Path == Archive).Bytes.AsSpan());
        Assert.Contains("../../spec/guide.md#bound", archived, StringComparison.Ordinal);
        Assert.Contains("../../images/a.png", archived, StringComparison.Ordinal);
        Assert.Contains("[target]: ../../spec/ref.md#part", archived, StringComparison.Ordinal);
        Assert.Contains("$[p](t)$", archived, StringComparison.Ordinal);
        Assert.Contains("[\n[p](t)\n]", archived, StringComparison.Ordinal);
    }

    [Fact]
    public void ProductionGatewayRetainsInjectedPolicyAndArchivedInputCannotBeReingested()
    {
        using var directory = new TemporaryDirectory();
        var raw = Fixture();
        WriteFiles(directory.Path, raw);
        TestGit.Run(directory.Path, "init");
        TestGit.Run(directory.Path, "add", ".");
        var repository = new GitRepositoryGateway(directory.Path);
        var result = RetireSourcesCommand.Run(directory.Path, repository, new FakeLeanReportSource(null), Args("archive", true));
        Assert.True(result.Success, result.Error);
        var after = ReadFiles(directory);
        Assert.Equal(raw.Entries.Single(entry => entry.Path == FileMapLoader.RelativePath).Bytes.ToArray(),
            after.Entries.Single(entry => entry.Path == FileMapLoader.RelativePath).Bytes.ToArray());
        var ingest = IngestCommand.RunReportFree(directory.Path, repository, ["--source", Archive]);
        Assert.False(ingest.Success);
        Assert.DoesNotContain(ReadFiles(directory).Entries, entry => entry.Path.StartsWith(
            BackfillInventoryLoader.RootPath + "source/", StringComparison.Ordinal));
    }

    [Fact]
    public void UnrelatedDeclaredSymlinkRemainsUsableAfterProductionRetirement()
    {
        using var directory = new TemporaryDirectory();
        var raw = Add(Fixture(), "docs/develop/archive/theory/Existing.md", "Existing archived material.\n");
        var policy = Encoding.UTF8.GetString(raw.Entries.Single(entry => entry.Path == FileMapLoader.RelativePath).Bytes.AsSpan());
        var linkPolicy = "{ pattern = \"docs/link.md\", kind = \"data\", admission_plane = \"content\", produced_by = \"none\", consumed_by = [\"reader\"], verified_by = [\"SnapshotDecoder\"], artifact_id = \"none\", runtime_disposition = \"committed-source\", symlink = { target = \"develop/archive/theory/Existing.md\", kind = \"file\" } }";
        raw = Replace(raw, FileMapLoader.RelativePath, policy.Replace("\n]\n[evidence", ",\n" + linkPolicy + "\n]\n[evidence", StringComparison.Ordinal));
        WriteFiles(directory.Path, raw);
        File.CreateSymbolicLink(Path.Combine(directory.Path, "docs/link.md"), "develop/archive/theory/Existing.md");
        TestGit.Run(directory.Path, "init");
        TestGit.Run(directory.Path, "add", ".");
        var result = RetireSourcesCommand.Run(directory.Path, new GitRepositoryGateway(directory.Path),
            new FakeLeanReportSource(null), Args("archive", true));
        Assert.True(result.Success, result.Error);
        Assert.Equal("develop/archive/theory/Existing.md", new FileInfo(Path.Combine(directory.Path, "docs/link.md")).LinkTarget);
        Assert.Equal("Existing archived material.\n", TemporaryFileSystem.File.ReadAllText(Path.Combine(directory.Path, "docs/link.md")));
    }

    [Theory]
    [InlineData("docs/latest.txt", "develop/theory/RetirementFixture.md")]
    [InlineData("CURRENT.md", "docs/develop/theory/RetirementFixture.md")]
    [InlineData("docs/z-atom.txt", "ledger")]
    public void DeclaredAliasesOutsideDocumentFiltersBlockRetirement(string linkPath, string target)
    {
        using var directory = new TemporaryDirectory();
        var raw = Fixture();
        if (target == "ledger") target = "../" + raw.Entries.First(entry => entry.Path.EndsWith(".yaml", StringComparison.Ordinal)).Path;
        var policy = Encoding.UTF8.GetString(raw.Entries.Single(entry => entry.Path == FileMapLoader.RelativePath).Bytes.AsSpan());
        var linkPolicy = "{ pattern = \"" + linkPath + "\", kind = \"data\", admission_plane = \"content\", produced_by = \"none\", consumed_by = [\"reader\"], verified_by = [\"SnapshotDecoder\"], artifact_id = \"none\", runtime_disposition = \"committed-source\", symlink = { target = \"" + target + "\", kind = \"file\" } }";
        raw = Replace(raw, FileMapLoader.RelativePath, linkPath.StartsWith("docs/", StringComparison.Ordinal)
            ? policy.Replace("\n]\n[evidence", ",\n" + linkPolicy + "\n]\n[evidence", StringComparison.Ordinal)
            : policy.Replace("files = [\n", "files = [\n" + linkPolicy + ",\n", StringComparison.Ordinal));
        WriteFiles(directory.Path, raw);
        File.CreateSymbolicLink(Path.Combine(directory.Path, linkPath), target);
        TestGit.Run(directory.Path, "init");
        TestGit.Run(directory.Path, "add", ".");
        var result = RetireSourcesCommand.Run(directory.Path, new GitRepositoryGateway(directory.Path),
            new FakeLeanReportSource(null), Args("archive", true));
        Assert.False(result.Success);
        Assert.True(result.Error.Contains("SOURCE_SYMLINK_REFERENCED", StringComparison.Ordinal), result.Error);
        Assert.True(File.Exists(Path.Combine(directory.Path, Source)));
        Assert.Equal(target, new FileInfo(Path.Combine(directory.Path, linkPath)).LinkTarget);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void TerminalForeignChildrenAreReusedWithoutRetiringTheirIncompleteOwner(bool sharedUnrecordedClaim)
    {
        const string text = "# Bundle\n\n## theorem 1.1\n\nFirst.\n\n## theorem 1.2\n\nSecond.\n";
        using var directory = new TemporaryDirectory();
        var fixture = new DecomposeFixture(text, AtomizerRegistry.GenericId);
        var decomposition = DecomposeAtomCommand.Run("synthetic", fixture.Gateway, fixture.Args(), fixture.Apply);
        Assert.True(decomposition.Success, decomposition.Error);
        var owner = Assert.Single(fixture.Document.RequireDigestionSources());
        var children = fixture.Document.RequireDigestionEntries().Single(entry => entry.AtomId == fixture.Parent.AtomId).Receipts.ChainAtoms;
        var childEntries = fixture.Document.RequireDigestionEntries().Where(entry => children.Contains(entry.AtomId)).ToArray();
        fixture.Current = Add(fixture.Current, BackfillInventoryLoader.RootPath + "foreign/source.toml",
            Encoding.UTF8.GetString(BackfillInventoryWriter.WriteSourceMetadata(owner with { SourceId = "foreign", SourcePath = "docs/foreign.md" }).AsSpan()));
        foreach (var entry in childEntries)
        {
            fixture.Replace(entry with { SourceId = "foreign", SourcePath = "docs/foreign.md" });
        }
        fixture.Current = Add(fixture.Current, "docs/foreign.md", text + "\n## Other\n\nStill unresolved.\n");
        fixture.Current = DigestionTestSupport.WithSourcePolicy(RawRepositorySnapshot.Create(
            fixture.Current.Entries.Where(entry => entry.Path != FileMapLoader.RelativePath)), ["docs/*.md"]);
        fixture.CaptureContext();
        var raw = RawRepositorySnapshot.Create(fixture.Current.Entries.Select(entry => RawRepositoryEntry.FromText(
            entry.Path == "docs/probe.md" ? Source : entry.Path,
            Encoding.UTF8.GetString(entry.Bytes.AsSpan()).Replace("docs/probe.md", Source, StringComparison.Ordinal))));
        WriteFiles(directory.Path, WithPolicy(raw, [Source, "docs/foreign.md"]));
        foreach (var id in children.Append(fixture.Parent.AtomId))
        {
            var contextInput = DigestionQuerySelection.ReadContext(Gateway(directory), id);
            var context = Assert.Single(DigestionAtomContextProjection.ResolveOccurrences(contextInput.Snapshot, contextInput.Document, id));
            var request = $"atom_id = '{id}'\njustification = 'Explanatory commentary.'\n"
                + $"previous_atom_id = '{context.Previous?.AtomId ?? "source-boundary"}'\nnext_atom_id = '{context.Next?.AtomId ?? "source-boundary"}'\n";
            var settled = SettleAtomCommandTests.Run(directory.Path, ReadFiles(directory), request);
            Assert.True(settled.Success, settled.Error);
        }
        if (sharedUnrecordedClaim)
            foreach (var path in new[] { Source, "docs/foreign.md" })
                File.AppendAllText(Path.Combine(directory.Path, path), "\n## New\n\nShared unresolved addition.\n");
        var before = ReadFiles(directory);
        var result = RetireSourcesCommand.Run(directory.Path, Gateway(directory), new FakeLeanReportSource(null),
            ["--source", "probe", "--mode", "archive", "--write"]);
        if (sharedUnrecordedClaim)
        {
            Assert.False(result.Success);
            Assert.Contains("SOURCE_HAS_RESIDUAL", result.Error, StringComparison.Ordinal);
            Assert.Equal(before.Entries.Select(entry => (entry.Path, Convert.ToHexString(entry.Bytes.AsSpan()))),
                ReadFiles(directory).Entries.Select(entry => (entry.Path, Convert.ToHexString(entry.Bytes.AsSpan()))));
            return;
        }
        Assert.True(result.Success, result.Error);
        var after = ReadFiles(directory);
        foreach (var original in before.Entries.Where(entry => entry.Path == "docs/foreign.md"
                     || entry.Path.StartsWith(BackfillInventoryLoader.RootPath + "foreign/", StringComparison.Ordinal)))
            Assert.Equal(original.Bytes.ToArray(), after.Entries.Single(entry => entry.Path == original.Path).Bytes.ToArray());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void FrozenCoverageIsRecheckedAndTheoremsArePreserved(bool staleEdge)
    {
        using var directory = new TemporaryDirectory();
        var defaults = new CoverSpec();
        var spec = defaults with { InitialCoverage = [defaults.Gid], Migration = "absorbed", Truth = "closed" };
        var inputs = spec.Materialize();
        var source = Assert.Single(inputs.Document.RequireDigestionSources());
        var raw = RawRepositorySnapshot.Create(inputs.Files.Where(pair => pair.Key != FileMapLoader.RelativePath)
            .Select(pair => RawRepositoryEntry.FromText(pair.Key == source.SourcePath ? Source : pair.Key,
                pair.Value.Replace(source.SourcePath, Source, StringComparison.Ordinal))));
        raw = RawRepositorySnapshot.Create(raw.Entries.Add(Fixture().Entries.Single(entry => entry.Path == FileMapLoader.RelativePath)));
        if (staleEdge)
            raw = RawRepositorySnapshot.Create(raw.Entries.Select(entry => entry.Path.EndsWith(".yaml", StringComparison.Ordinal)
                && entry.Path.StartsWith(BackfillInventoryLoader.RootPath, StringComparison.Ordinal)
                    ? RawRepositoryEntry.FromText(entry.Path, Encoding.UTF8.GetString(entry.Bytes.AsSpan())
                        .Replace(spec.TargetStatementId, FrozenStatementReceiptTestData.Id('b'), StringComparison.Ordinal)) : entry));
        WriteFiles(directory.Path, raw);
        var before = Image(directory);
        var report = new FakeLeanReportSource(inputs.Report);
        var result = RetireSourcesCommand.Run(directory.Path, Gateway(directory), report,
            ["--source", source.SourceId, "--mode", "delete", "--write"]);
        if (staleEdge)
        {
            Assert.False(result.Success);
            Assert.Equal(before, Image(directory));
        }
        else
        {
            Assert.True(result.Success, result.Error);
            var after = ReadFiles(directory);
            foreach (var original in raw.Entries.Where(entry => entry.Path.StartsWith("D5/", StringComparison.Ordinal)
                         || entry.Path.StartsWith("Golden/Frozen/", StringComparison.Ordinal)))
                Assert.Equal(original.Bytes.ToArray(), after.Entries.Single(entry => entry.Path == original.Path).Bytes.ToArray());
            Assert.True(report.CallCount > 0);
        }
    }

    private static string[] Args(string mode, bool write = false) =>
        write ? ["--source", "source", "--mode", mode, "--write"] : ["--source", "source", "--mode", mode];

    private static FakeRepositoryGateway Gateway(TemporaryDirectory directory) =>
        new(RawChangeSet.Create([]), null, null, currentReader: () => ReadFiles(directory));

    private static RawRepositorySnapshot Fixture(bool terminal = true, string text = AtomContextFixture.ThreeClaims)
    {
        var fixture = AtomContextFixture.Create(text);
        if (terminal)
        {
            var snapshot = fixture.Snapshot();
            var document = fixture.Ledger;
            fixture = fixture.WithEntries(document.RequireDigestionEntries().Select(entry =>
            {
                var context = Assert.Single(DigestionAtomContextProjection.ResolveOccurrences(snapshot, document, entry.AtomId));
                return entry with
                {
                    ProjectedStatus = new(DigestionMigrationState.Nonpropositional, DigestionTruthState.Inapplicable),
                    Receipts = entry.Receipts with
                    {
                        Nonpropositional = new("Explanatory commentary without a mathematical proposition.", context.Previous?.AtomId, context.Next?.AtomId),
                    },
                };
            }));
        }
        var raw = RawRepositorySnapshot.Create(fixture.RawSnapshot().Entries.Select(entry =>
            RawRepositoryEntry.FromText(entry.Path == AtomContextFixture.SourcePath ? Source : entry.Path,
                Encoding.UTF8.GetString(entry.Bytes.AsSpan()).Replace(AtomContextFixture.SourcePath, Source, StringComparison.Ordinal))));
        raw = WithPolicy(raw, [Source]);
        raw = Add(raw, "D5/Retained.lean", "theorem retained : True := True.intro\n");
        raw = Add(raw, BackfillInventoryLoader.RootPath + "unrelated/source.toml", "intentionally invalid unrelated metadata = [");
        return raw;
    }

    private static RawRepositorySnapshot WithPolicy(RawRepositorySnapshot raw, string[] sources)
    {
        raw = DigestionTestSupport.WithSourcePolicy(RawRepositorySnapshot.Create(raw.Entries.Where(entry => entry.Path != FileMapLoader.RelativePath)), sources);
        var policy = Encoding.UTF8.GetString(raw.Entries.Single(entry => entry.Path == FileMapLoader.RelativePath).Bytes.AsSpan());
        var archivePolicy = "{ pattern = \"docs/develop/archive/theory/**\", kind = \"data\", admission_plane = \"content\", produced_by = \"none\", consumed_by = [\"reader\"], verified_by = [\"SnapshotDecoder\"], artifact_id = \"none\", runtime_disposition = \"committed-source\" }";
        raw = Replace(raw, FileMapLoader.RelativePath, policy.Replace("files = [\n", "files = [\n" + archivePolicy + ",\n", StringComparison.Ordinal));
        return raw;
    }

    private static RawRepositorySnapshot BatchFixture(bool linkSources = false)
    {
        const string secondSource = "docs/develop/theory/SecondFixture.md";
        var first = Fixture(text: AtomContextFixture.ThreeClaims
            + (linkSources ? "\n[other](Second%46ixture.md#section)\n" : string.Empty));
        var second = Fixture(text: AtomContextFixture.ThreeClaims.Replace("Before", "SecondBefore", StringComparison.Ordinal)
            .Replace("Middle", "SecondMiddle", StringComparison.Ordinal).Replace("After", "SecondAfter", StringComparison.Ordinal)
            + (linkSources ? "\n[other](Retirement%46ixture.md#section)\n" : string.Empty));
        var renamed = second.Entries.Select(entry => RawRepositoryEntry.FromText(
            entry.Path.Replace(BackfillInventoryLoader.RootPath + "source/", BackfillInventoryLoader.RootPath + "second/", StringComparison.Ordinal)
                .Replace(Source, secondSource, StringComparison.Ordinal),
            Encoding.UTF8.GetString(entry.Bytes.AsSpan()).Replace(Source, secondSource, StringComparison.Ordinal)
                .Replace("\"source\"", "\"second\"", StringComparison.Ordinal)));
        return WithPolicy(RawRepositorySnapshot.Create(first.Entries.Concat(renamed).GroupBy(entry => entry.Path)
            .Select(group => group.First())), [Source, secondSource]);
    }

    private static RawRepositorySnapshot Add(RawRepositorySnapshot raw, string path, string text) =>
        RawRepositorySnapshot.Create(raw.Entries.Add(RawRepositoryEntry.FromText(path, text)));

    private static RawRepositorySnapshot Replace(RawRepositorySnapshot raw, string path, string text) =>
        RawRepositorySnapshot.Create(raw.Entries.Select(entry => entry.Path == path ? RawRepositoryEntry.FromText(path, text) : entry));
}
