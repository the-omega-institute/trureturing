using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DecomposeAtomTests
{
    [Fact]
    public void DeclaredDialectWritesExactBoldClauseChain()
    {
        var f = new DecomposeFixture();
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(), f.Apply);
        Assert.True(result.Success, result.Error);
        Assert.Contains("DECOMPOSE_WRITTEN", result.Output, StringComparison.Ordinal);
        var parent = Assert.Single(f.Document.RequireDigestionEntries(), e => e.AtomId == f.Parent.AtomId);
        Assert.Equal(2, parent.Receipts.ChainAtoms.Length);
        Assert.Equal(2, f.CasWrites.Length);
        Assert.Equal(DecomposeFixture.Bold, string.Concat(parent.Receipts.ChainAtoms.Select(id =>
            Encoding.UTF8.GetString(f.Current.Entries.Single(e => e.Path == DigestionCasStore.RootPath + id).Bytes.AsSpan()))));
        Assert.Equal(1, f.Writes);
        Assert.Equal(["baseline"], f.Gateway.ReadRevisionCalls);
    }

    [Fact]
    public void TitlePreambleAndClosingRemarkAreLosslessClaimBytes()
    {
        var f = new DecomposeFixture(DecomposeFixture.Eight);
        var plan = DigestionDecomposition.Plan(f.Parent, DecomposeFixture.Atom(DecomposeFixture.Eight).RawBytes,
            AtomizerRegistry.Require(DecomposeFixture.Dialect).Atomize, f.Rules);
        Assert.Equal(8, plan.Children.Length);
        Assert.All(plan.Segments, s => Assert.Equal(DigestionSegmentKind.Claim, s.Kind));
        Assert.Equal(DecomposeFixture.Eight, Encoding.UTF8.GetString(
            plan.Segments.SelectMany(s => s.Atom.RawBytes).ToArray()));
        Assert.Null(DigestionDecomposition.IntegrityFailure(plan));
        Assert.Equal(0, plan.Segments[0].Atom.StartByte);
        Assert.Equal(Encoding.UTF8.GetByteCount(DecomposeFixture.Eight), plan.Segments[^1].Atom.EndByte);
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(), f.Apply);
        Assert.True(result.Success, result.Error);
        Assert.Equal(9, f.Document.RequireDigestionEntries().Length);
        Assert.Equal(DecomposeFixture.Eight, Encoding.UTF8.GetString(f.CasWrites.SelectMany(c => c.Bytes).ToArray()));
    }

    [Fact]
    public void NestedChainChildCanBeDecomposedAndAlignerValidatesBothLevels()
    {
        const string nested = "**Theorem 1.1** First assertion.\n\n**Bundle**\n\nPreamble.\n\n- alpha\n- beta\n";
        var f = new DecomposeFixture(nested);
        var first = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(), f.Apply);
        Assert.True(first.Success, first.Error);
        var nestedEntry = Assert.Single(f.Document.RequireDigestionEntries(), e =>
            e.AtomId != f.Parent.AtomId && f.Snapshot.TryGetFile(DigestionCasStore.RootPath + e.AtomId, out var blob)
            && DigestionDecompositionPolicy.IsMultiClause(DigestionAtom.FromFrozenCas(blob.RawBytes)));
        var second = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(nestedEntry.AtomId), f.Apply);
        Assert.True(second.Success, second.Error);
        var alignment = DigestionLedgerAligner.Evaluate(f.Document, f.Snapshot, f.Document, DigestionAlignmentMode.Ingest);
        Assert.Empty(alignment.Findings);
        Assert.Contains(f.Parent.AtomId, alignment.VerifiedClausePlanParents);
        Assert.Contains(nestedEntry.AtomId, alignment.VerifiedClausePlanParents);
        Assert.Equal(2, f.Writes);
    }

    [Theory]
    [InlineData("covered", "PARENT_STATE")]
    [InlineData("quarantine", "QUARANTINED")]
    [InlineData("missing-cas", "CAS_MISSING")]
    [InlineData("corrupt-cas", "CAS_MISMATCH")]
    [InlineData("single", "NO_CLAUSE_PLAN")]
    [InlineData("ambiguous", "AMBIGUOUS")]
    [InlineData("unknown-dialect", "Unknown declared dialect")]
    public void InvalidParentsFailWithoutWrites(string defect, string code)
    {
        var text = defect switch
        {
            "single" => "**Theorem 1.1** Single assertion.\n",
            "ambiguous" => "**Theorem 1.1**\n\n- repeated\n- repeated\n",
            _ => DecomposeFixture.Bold,
        };
        var f = new DecomposeFixture(text, defect == "unknown-dialect" ? "dialect:missing" : DecomposeFixture.Dialect);
        if (defect == "covered") f.Replace(f.Parent with
        {
            ProjectedStatus = new DigestionStatus(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
        });
        if (defect == "quarantine") f.Replace(f.Parent with
        {
            Receipts = f.Parent.Receipts with { Quarantine = new DigestionQuarantine("blocked", "supply witness", "missing-prerequisite") },
        });
        if (defect is "missing-cas" or "corrupt-cas")
        {
            f.Current = RawRepositorySnapshot.Create(f.Current.Entries
                .Where(e => e.Path != DigestionCasStore.RootPath + f.Parent.AtomId)
                .Concat(defect == "corrupt-cas" ? new[] { RawRepositoryEntry.FromText(DigestionCasStore.RootPath + f.Parent.AtomId, "wrong\n") } : []));
        }
        var before = f.Current;
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(), f.Apply);
        Assert.False(result.Success);
        Assert.Contains("DECOMPOSE_INVALID", result.Error, StringComparison.Ordinal);
        Assert.Contains(code, result.Error, StringComparison.Ordinal);
        Assert.Equal(0, f.Writes);
        Assert.Same(before, f.Current);
    }

    [Theory]
    [InlineData("gap")]
    [InlineData("overlap")]
    [InlineData("unknown-kind")]
    public void InvalidPlansFailWithoutWrites(string defect)
    {
        var f = new DecomposeFixture();
        TheoryAtomizer malformed = (bytes, rules) =>
        {
            var parent = DigestionAtom.FromFrozenCas([.. bytes]);
            var first = parent with { EndByte = 20, RawBytes = parent.RawBytes[..20] };
            first = first with { Fingerprints = DigestionFingerprint.Compute(first.RawBytes.AsSpan()) };
            var start = defect switch { "gap" => 21, "overlap" => 19, _ => 20 };
            var last = parent with { StartByte = start, RawBytes = parent.RawBytes[start..] };
            last = last with { Fingerprints = DigestionFingerprint.Compute(last.RawBytes.AsSpan()) };
            var plan = new DigestionClausePlan(parent,
                ImmutableArray.Create(new DigestionSegment(defect == "unknown-kind" ? (DigestionSegmentKind)99 : DigestionSegmentKind.Claim, first),
                    new DigestionSegment(DigestionSegmentKind.Claim, last)));
            return new AtomizedTheoryDocument([parent], [new DigestionSlice(true, parent.RawBytes)], [plan], GenreRegistryCheck.Collected([]));
        };
        var before = f.Current;
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(), f.Apply, _ => malformed);
        Assert.False(result.Success);
        Assert.Contains("DECOMPOSE_INVALID", result.Error, StringComparison.Ordinal);
        if (defect == "unknown-kind")
            Assert.Contains("clause plan has unknown segment kind", result.Error, StringComparison.Ordinal);
        Assert.Equal(0, f.Writes);
        Assert.Same(before, f.Current);
    }

    [Fact]
    public void UnknownSegmentKindHasExactIntegrityFailureWithValidTiling()
    {
        var parent = DecomposeFixture.Atom(DecomposeFixture.Bold);
        var first = DigestionAtom.FromFrozenCas(parent.RawBytes[..20]);
        var last = DigestionAtom.FromFrozenCas(parent.RawBytes[20..]) with
        {
            StartByte = 20,
            EndByte = parent.EndByte,
        };
        var known = new DigestionClausePlan(parent, ImmutableArray.Create(
            new DigestionSegment(DigestionSegmentKind.Claim, first),
            new DigestionSegment(DigestionSegmentKind.Claim, last)));
        Assert.Null(DigestionDecomposition.IntegrityFailure(known));

        var unknown = new DigestionClausePlan(parent, known.Segments.SetItem(0,
            new DigestionSegment((DigestionSegmentKind)99, first)));
        Assert.Equal("clause plan has unknown segment kind", DigestionDecomposition.IntegrityFailure(unknown));
    }

    [Fact]
    public void DryRunPrintsExactWriteSetWithoutApplyingTransaction()
    {
        var f = new DecomposeFixture(DecomposeFixture.Eight);
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(dryRun: true), f.Apply);
        Assert.True(result.Success, result.Error);
        Assert.DoesNotContain("type=structural", result.Output, StringComparison.Ordinal);
        Assert.Equal(8, result.Output.Split('\n').Count(line => line.Contains("type=claim", StringComparison.Ordinal)));
        Assert.Contains("start=0", result.Output, StringComparison.Ordinal);
        Assert.Contains("dry_run=true", result.Output, StringComparison.Ordinal);
        Assert.Equal(0, f.Writes);
        Assert.Same(f.Baseline, f.Current);
    }

    [Fact]
    public void RepeatedRunIsAByteNoOp()
    {
        var f = new DecomposeFixture();
        Assert.True(DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(), f.Apply).Success);
        var before = f.Current;
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(), f.Apply);
        Assert.True(result.Success, result.Error);
        Assert.Same(before, f.Current);
        Assert.Equal(1, f.Writes);
    }

    [Fact]
    public void SharedIdentityReusesExistingEntryAndCas()
    {
        const string shared = "**Second** Second assertion.\n";
        var f = new DecomposeFixture();
        var child = DecomposeFixture.Entry(shared);
        f.Add(child, shared);
        var prior = f.Current.Entries.Single(e => e.Path == DecomposeFixture.PathFor(child));
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(), f.Apply);
        Assert.True(result.Success, result.Error);
        Assert.Single(f.Document.RequireDigestionEntries(), e => e.AtomId == child.AtomId);
        Assert.DoesNotContain(f.LedgerWrites, e => e.Path == prior.Path);
        Assert.DoesNotContain(f.CasWrites, e => e.Reference == child.CasRef);
        Assert.Same(prior, f.Current.Entries.Single(e => e.Path == prior.Path));
    }

    [Theory]
    [InlineData("open")]
    [InlineData("closed")]
    [InlineData("tail")]
    public void PartialParentsRetainCoverageAndStatus(string truth)
    {
        var f = new DecomposeFixture();
        var parent = f.Parent with
        {
            ProjectedStatus = new DigestionStatus(DigestionMigrationState.Partial, Enum.Parse<DigestionTruthState>(truth, true)),
            Coverage = [new DigestionCoverageEdge("D5/S0/Carrier/Probe.probe", null)],
        };
        f.Replace(parent);
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(), f.Apply);
        Assert.True(result.Success, result.Error);
        var updated = Assert.Single(f.Document.RequireDigestionEntries(), e => e.AtomId == parent.AtomId);
        Assert.Equal(parent.ProjectedStatus, updated.ProjectedStatus);
        Assert.Equal(parent.Coverage.ToArray(), updated.Coverage.ToArray());
    }

    [Fact]
    public void AlignerValidatesProducedPlanWithoutWritingBacklog()
    {
        var f = new DecomposeFixture(DecomposeFixture.Eight);
        var untouched = DigestionLedgerAligner.Evaluate(f.Document, f.Snapshot, f.Document, DigestionAlignmentMode.Ingest);
        Assert.Empty(Assert.Single(f.Document.RequireDigestionEntries()).Receipts.ChainAtoms);
        Assert.Empty(untouched.Findings);
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(), f.Apply);
        Assert.True(result.Success, result.Error);
        var alignment = DigestionLedgerAligner.Evaluate(f.Document, f.Snapshot, f.Document, DigestionAlignmentMode.Ingest);
        Assert.Empty(alignment.Findings);
        Assert.Contains(f.Parent.AtomId, alignment.VerifiedClausePlanParents);
    }

    [Fact]
    public void NewAbsorptionGuardStillRejectsUndecomposedParent()
    {
        var atom = DecomposeFixture.Atom(DecomposeFixture.Eight);
        Assert.True(DigestionDecompositionPolicy.RejectsNewAbsorption(atom,
            DigestionMigrationState.Absorbed, 0, false, DigestionMigrationState.Residual));
        Assert.False(DigestionDecompositionPolicy.RejectsNewAbsorption(atom,
            DigestionMigrationState.Absorbed, 0, true, DigestionMigrationState.Residual));
    }

    [Fact]
    public void CliDispatchesDecomposeDryRunThroughProductionEnvironment()
    {
        var f = new DecomposeFixture();
        var environment = new ProductionCliEnvironment("synthetic", f.Gateway,
            new FakeLeanReportSource(null), new FakeScribeEmissionVerifier(null));
        var console = new BufferedConsole();
        var exit = CliApplication.Run(["decompose-atom", .. f.Args(dryRun: true)], environment, console);
        Assert.Equal(0, exit);
        Assert.Contains("DECOMPOSE_WRITTEN", console.Output, StringComparison.Ordinal);
        Assert.Same(f.Baseline, f.Current);
    }

    [Fact]
    public void TransactionFailureRollsBackOnlyNewCasAndDoesNotPublishSuccess()
    {
        var f = new DecomposeFixture();
        var created = new HashSet<string>(StringComparer.Ordinal) { "preexisting" };
        var rolledBack = false;
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(),
            (root, current, cas, updates) => IngestCommand.ApplyDecompositionAtomically(
                root, current, cas, updates,
                (_, objects) =>
                {
                    foreach (var item in objects) created.Add(item.RelativePath);
                    return objects.Select(static item => item.RelativePath).ToImmutableArray();
                },
                (_, _, _) => throw new IOException("injected ledger commit failure"),
                (paths, _) =>
                {
                    foreach (var path in paths) created.Remove(path);
                    rolledBack = true;
                }));
        Assert.False(result.Success);
        Assert.Contains("injected ledger commit failure", result.Error, StringComparison.Ordinal);
        Assert.Empty(result.Output);
        Assert.True(rolledBack);
        Assert.Equal(["preexisting"], created);
        Assert.Same(f.Baseline, f.Current);
    }

    [Fact]
    public void IngestReusesChildAdmittedByAnEarlierSourceWithoutAClausePlan()
    {
        const string shared = "**Theorem 1.1** Shared.\n\n";
        const string other = "**Second** Other.\n";
        var first = new DigestionLedgerSource("a-single", "docs/single.md", AtomizerRegistry.GenericId,
            [], GenreRegistryProjection.Available(GenreRegistryCheck.Collected([])), []);
        var second = first with { SourceId = "b-bundle", SourcePath = "docs/bundle.md" };
        var raw = RawRepositorySnapshot.Create(
        [
            RawRepositoryEntry.FromText(TheoryAtomizerDataLoader.DataPath, DecomposeFixture.RulesText),
            RawRepositoryEntry.FromText("docs/single.md", shared),
            RawRepositoryEntry.FromText("docs/bundle.md", shared + other),
            new RawRepositoryEntry("Meta/Digestion/backfill/a-single/source.toml",
                BackfillInventoryWriter.WriteSourceMetadata(first)),
            new RawRepositoryEntry("Meta/Digestion/backfill/b-bundle/source.toml",
                BackfillInventoryWriter.WriteSourceMetadata(second)),
        ]);
        var snapshot = DecomposeFixture.Decode(raw);
        var document = BackfillInventoryLoader.Load(snapshot);
        var plan = DigestionIngestor.Plan(document, snapshot, document);

        var admitted = plan.AdmissionDocument.RequireDigestionEntries();
        Assert.Equal(3, admitted.Length);
        Assert.Equal(3, admitted.Select(entry => entry.AtomId).Distinct(StringComparer.Ordinal).Count());
        Assert.Equal(3, plan.ResidualOpenAdded);
        Assert.Equal(3, plan.CasObjects.Length);
        var child = Assert.Single(admitted, entry => entry.Fingerprints == DecomposeFixture.Atom(shared).Fingerprints);
        Assert.Equal("a-single", child.SourceId);
        Assert.Equal("docs/single.md", child.SourcePath);
        var parent = Assert.Single(admitted, entry => !entry.Receipts.ChainAtoms.IsEmpty);
        Assert.Equal("b-bundle", parent.SourceId);
        Assert.Equal([child.AtomId, DecomposeFixture.Atom(other).Fingerprints.RawSha256[7..]],
            parent.Receipts.ChainAtoms.ToArray());
        Assert.Equal(3, plan.Document.RequireDigestionEntries().Length);
    }

    [Fact]
    public void IngestUsesDeclaredLosslessPlanAndCanonicalChildMaterialization()
    {
        var f = new DecomposeFixture(DecomposeFixture.Eight);
        var plan = DigestionIngestor.Plan(f.Document, f.Snapshot, f.Document);
        Assert.Equal(8, plan.ResidualOpenAdded);
        Assert.Equal(8, plan.CasObjects.Length);
        var parent = Assert.Single(plan.Document.RequireDigestionEntries(), e => e.AtomId == f.Parent.AtomId);
        Assert.Equal(8, parent.Receipts.ChainAtoms.Length);
        Assert.Equal(DecomposeFixture.Eight, Encoding.UTF8.GetString(parent.Receipts.ChainAtoms
            .SelectMany(id => plan.CasObjects.Single(item => item.Reference == "sha256:" + id).Bytes).ToArray()));
    }

    [Fact]
    public void NestedChildrenInheritTheirParentContentDisposition()
    {
        const string nested = "**Theorem 1.1** First assertion.\n\n**Bundle**\n\nPreamble.\n\n- alpha\n- beta\n";
        var f = new DecomposeFixture(nested);
        Assert.True(DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(), f.Apply).Success);
        var child = Assert.Single(f.Document.RequireDigestionEntries(), e => e.AtomId != f.Parent.AtomId
            && f.Snapshot.TryGetFile(DigestionCasStore.RootPath + e.AtomId, out var blob)
            && DigestionDecompositionPolicy.IsMultiClause(DigestionAtom.FromFrozenCas(blob.RawBytes)));
        Assert.True(DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(child.AtomId), f.Apply).Success);
        var kinds = DigestionContentKindResolver.Resolve(f.Snapshot, f.Document);
        Assert.All(f.Document.RequireDigestionEntries(), e => Assert.Equal("theorem", kinds[e.AtomId]));
    }

    [Fact]
    public void ContextBoundAtomizerDecomposesFrozenCasAndPreservesChildKinds()
    {
        const string text = "**\u5b9a\u7406 1.1 (Fixture)[\u8bc1]\u3002**\n\n- alpha\n- beta\n";
        var f = new DecomposeFixture(text, AtomizerRegistry.ConeId);
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Select(entry => entry.Path == "docs/probe.md"
            ? RawRepositoryEntry.FromText("docs/probe.md", "# Cone\n\n## \u7b2c\u4e00\u7ae0\n\n" + text)
            : entry));
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(), f.Apply);
        Assert.True(result.Success, result.Error);
        Assert.Equal(3, f.Document.RequireDigestionEntries().Length);
        var kinds = DigestionContentKindResolver.Resolve(f.Snapshot, f.Document);
        Assert.All(f.Document.RequireDigestionEntries(), entry => Assert.Equal("theorem", kinds[entry.AtomId]));
        Assert.Empty(DigestionLedgerAligner.Evaluate(f.Document, f.Snapshot, f.Document, DigestionAlignmentMode.Ingest).Findings);
    }

    [Fact]
    public void UnicodeAndCrLfRangesReassembleImmutableCasExactly()
    {
        const string text = "**Theorem 1.1**\r\n\r\nPreamble \u03b1.\r\n\r\n- first \u03b2\r\n- second \u03b3\r\n";
        var f = new DecomposeFixture(text);
        var plan = DigestionDecomposition.Plan(f.Parent, DecomposeFixture.Atom(text).RawBytes,
            AtomizerRegistry.Require(DecomposeFixture.Dialect).Atomize, f.Rules);
        Assert.Equal(Encoding.UTF8.GetBytes(text), plan.Segments.SelectMany(s => s.Atom.RawBytes).ToArray());
        Assert.Equal(2, plan.Children.Length);
        Assert.Null(DigestionDecomposition.IntegrityFailure(plan));
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(), f.Apply);
        Assert.True(result.Success, result.Error);
    }
}
