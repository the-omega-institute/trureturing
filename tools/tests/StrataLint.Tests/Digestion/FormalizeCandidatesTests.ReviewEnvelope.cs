using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

// review-envelope 的派生规则钉子(#4163)。作为 FormalizeCandidatesTests 的 partial 以复用其合成
// 账本夹具(Entry / Ledger / AddLedgerFiles / ValidReceipt),不复制夹具代码。
public sealed partial class FormalizeCandidatesTests
{
    [Fact]
    public void ReviewEnvelopeReportsReceiptsAddedBetweenBaseAndHeadAsDeposited()
    {
        var entry = Entry("source", "deposited-atom", "theorem", "1.0", atomizer: AtomizerRegistry.GenericId);
        var baseSnapshot = ReviewSnapshot([entry], quarantined: [], receipted: []);
        var headSnapshot = ReviewSnapshot([entry], quarantined: [], receipted: [entry]);

        var derivation = ReviewEnvelopeCommand.Derive(baseSnapshot, headSnapshot);

        var deposited = Assert.Single(derivation.DepositedAtoms);
        Assert.Equal("deposited-atom", deposited.AtomId);
        Assert.Equal("D5/S0/Synthetic/Receipt.deposited_atom", deposited.Gid);
        Assert.Empty(derivation.EjectedAtoms);
    }

    [Fact]
    public void ReviewEnvelopeReportsQuarantineBlocksAddedInHeadAsEjected()
    {
        var entry = Entry("source", "ejected-atom", "theorem", "1.0", atomizer: AtomizerRegistry.GenericId);
        var baseSnapshot = ReviewSnapshot([entry], quarantined: [], receipted: []);
        var headSnapshot = ReviewSnapshot([entry], quarantined: [entry], receipted: []);

        var derivation = ReviewEnvelopeCommand.Derive(baseSnapshot, headSnapshot);

        Assert.Empty(derivation.DepositedAtoms);
        var ejected = Assert.Single(derivation.EjectedAtoms);
        Assert.Equal("ejected-atom", ejected.AtomId);
        Assert.Equal("missing-prerequisite", ejected.BlockerClass);
        Assert.Equal("public owner exists", ejected.ReentryCondition);
    }

    [Fact]
    public void ReviewEnvelopeDoesNotReportAQuarantineAlreadyPresentInBase()
    {
        var stale = Entry("source", "already-quarantined", "theorem", "1.0", atomizer: AtomizerRegistry.GenericId);
        var fresh = Entry("source", "fresh-deposit", "theorem", "2.0", atomizer: AtomizerRegistry.GenericId);
        var baseSnapshot = ReviewSnapshot([stale, fresh], quarantined: [stale], receipted: []);
        var headSnapshot = ReviewSnapshot([stale, fresh], quarantined: [stale], receipted: [fresh]);

        var derivation = ReviewEnvelopeCommand.Derive(baseSnapshot, headSnapshot);

        Assert.Empty(derivation.EjectedAtoms);
        Assert.Equal("fresh-deposit", Assert.Single(derivation.DepositedAtoms).AtomId);
    }

    [Fact]
    public void ReviewEnvelopeFailsClosedWhenAQuarantinedAtomAlsoHoldsAReceiptInHead()
    {
        // 隔离块早在 base 里,本次只加了收据 —— 仍是矛盾:互斥按 head 全域判,不按本次 diff。
        var entry = Entry("source", "both", "theorem", "1.0", atomizer: AtomizerRegistry.GenericId);
        var baseSnapshot = ReviewSnapshot([entry], quarantined: [entry], receipted: []);
        var headSnapshot = ReviewSnapshot([entry], quarantined: [entry], receipted: [entry]);

        var exception = Assert.Throws<FormatException>(
            () => ReviewEnvelopeCommand.Derive(baseSnapshot, headSnapshot));

        // 互斥由账本 loader 执法,命令把它作为 FormatException 原样上抛(Run 渲染为 REVIEW_ENVELOPE_INVALID)。
        Assert.Contains("cannot be quarantined", exception.Message, StringComparison.Ordinal);
        Assert.Contains("both", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ReviewEnvelopeFailsClosedWhenHeadAddsNoOutcome()
    {
        var entry = Entry("source", "unchanged", "theorem", "1.0", atomizer: AtomizerRegistry.GenericId);
        var snapshot = ReviewSnapshot([entry], quarantined: [], receipted: []);

        var exception = Assert.Throws<FormatException>(
            () => ReviewEnvelopeCommand.Derive(snapshot, snapshot));

        Assert.Contains("no outcome", exception.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("--base")]
    [InlineData("--head", "abc")]
    [InlineData("--base", "a", "--head", "b", "--extra")]
    public void ReviewEnvelopeUsageErrorsFailClosedWithTheInvalidMarker(params string[] arguments)
    {
        var entry = Entry("source", "any", "theorem", "1.0", atomizer: AtomizerRegistry.GenericId);
        var snapshot = ReviewSnapshot([entry], quarantined: [], receipted: []);
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), snapshot, snapshot);

        var result = ReviewEnvelopeCommand.Run(gateway, arguments);

        Assert.False(result.Success);
        Assert.StartsWith(ReviewEnvelopeCommand.InvalidMarker, result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ReviewEnvelopeCommandRendersBranchTruthAsJsonThroughTheGateway()
    {
        var entry = Entry("source", "rendered", "theorem", "1.0", atomizer: AtomizerRegistry.GenericId);
        var baseSnapshot = ReviewSnapshot([entry], quarantined: [], receipted: []);
        var headSnapshot = ReviewSnapshot([entry], quarantined: [], receipted: [entry]);
        var gateway = new RevisionKeyedGateway(new Dictionary<string, RawRepositorySnapshot>(StringComparer.Ordinal)
        {
            ["base-sha"] = baseSnapshot,
            ["head-sha"] = headSnapshot,
        });

        var result = ReviewEnvelopeCommand.Run(gateway, ["--base", "base-sha", "--head", "head-sha"]);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal(ReviewEnvelopeCommand.Schema, json.RootElement.GetProperty("schema").GetString());
        Assert.Equal("base-sha", json.RootElement.GetProperty("base").GetString());
        Assert.Equal("head-sha", json.RootElement.GetProperty("head").GetString());
        Assert.Equal("rendered", Assert.Single(json.RootElement.GetProperty("deposited").EnumerateArray()).GetProperty("atom_id").GetString());
        Assert.Empty(json.RootElement.GetProperty("ejected").EnumerateArray());
    }

    [Fact]
    public void ReviewEnvelopeVerbIsRegistered()
    {
        Assert.Contains("review-envelope", CliApplication.ImplementedCommands);
    }

    // 合成快照:规则文件(Minimal)、账本(按 quarantined 集合给条目加隔离块)、源文与 CAS、以及 receipted
    // 集合的收据。两棵快照的差别只在 quarantined / receipted 两个集合,派生规则由此可被逐条钉住。
    private static RawRepositorySnapshot ReviewSnapshot(
        IReadOnlyList<EntryFixture> entries,
        IReadOnlyList<EntryFixture> quarantined,
        IReadOnlyList<EntryFixture> receipted)
    {
        var quarantinedIds = quarantined.Select(static entry => entry.AtomId).ToHashSet(StringComparer.Ordinal);
        var ledger = Ledger(entries, AtomizerRegistry.GenericId);
        var source = Assert.Single(ledger.RequireDigestionSources());
        ledger = ledger.WithDigestionSources(
        [
            source with
            {
                Entries = source.Entries
                    .Select(stored => quarantinedIds.Contains(stored.AtomId)
                        ? stored with
                        {
                            Receipts = stored.Receipts with
                            {
                                Quarantine = new DigestionQuarantine(
                                    "no public owner in D5; pinned Mathlib miss",
                                    "public owner exists",
                                    "missing-prerequisite"),
                            },
                        }
                        : stored)
                    .ToImmutableArray(),
            },
        ]);
        var files = new List<RawRepositoryEntry>
        {
            new(TheoryAtomizerDataLoader.DataPath,
                ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(TheoryAtomizerDataTests.Minimal))),
        };
        AddLedgerFiles(files, ledger);
        files.Add(new RawRepositoryEntry(
            "synthetic/source.md",
            ImmutableArray.CreateRange(entries.SelectMany(static entry => entry.Atom.RawBytes))));
        foreach (var entry in entries)
        {
            var captured = DigestionCasStore.Capture(entry.Atom.RawBytes.AsSpan());
            files.Add(new RawRepositoryEntry(captured.RelativePath, captured.Bytes));
        }
        foreach (var entry in receipted)
        {
            files.Add(new RawRepositoryEntry(
                DigestionFormalizationReceipt.RootPath + entry.AtomId + DigestionFormalizationReceipt.PathSuffix,
                ImmutableArray.CreateRange(ValidReceipt(entry))));
        }
        return RawRepositorySnapshot.Create(files);
    }

    private sealed class RevisionKeyedGateway(IReadOnlyDictionary<string, RawRepositorySnapshot> revisions)
        : IRepositoryGateway
    {
        public AdmissionTopologyOutcome InspectAdmissionTopology() => throw new NotSupportedException();

        public PreparedRepository Prepare(string? protectedBase) => throw new NotSupportedException();

        public FrozenRevisionIdentity ResolveCurrentRevision() => throw new NotSupportedException();

        public RawRepositorySnapshot ReadCurrent() => throw new NotSupportedException();

        public RawRepositorySnapshot ReadRevision(string revision) => revisions[revision];

        public RawChangeSet ReadCurrentChanges() => throw new NotSupportedException();

        public RawChangeSet ReadChanges(string protectedBase) => throw new NotSupportedException();
    }
}
