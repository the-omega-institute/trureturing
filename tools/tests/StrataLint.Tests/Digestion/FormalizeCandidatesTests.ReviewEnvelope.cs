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

        var exception = Assert.ThrowsAny<FormatException>(
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
    public void ReviewEnvelopeRejectsAReceiptWhosePathDoesNotMatchItsAtomId()
    {
        var real = Entry("source", "real-atom", "theorem", "1.0", atomizer: AtomizerRegistry.GenericId);
        var other = Entry("source", "other-atom", "theorem", "2.0", atomizer: AtomizerRegistry.GenericId);
        var baseSnapshot = ReviewSnapshot([real, other], quarantined: [], receipted: []);
        // 收据字节属于 real-atom,却放在 other-atom 的路径下。
        var headFiles = ReviewSnapshot([real, other], quarantined: [], receipted: []).Entries.ToList();
        headFiles.Add(new RawRepositoryEntry(
            DigestionFormalizationReceipt.PathForAtom("other-atom"),
            ImmutableArray.CreateRange(ValidReceipt(real))));

        var exception = Assert.Throws<FormatException>(
            () => ReviewEnvelopeCommand.Derive(baseSnapshot, RawRepositorySnapshot.Create(headFiles)));

        Assert.Contains("path/atom mismatch", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ReviewEnvelopeRejectsAReceiptForAnAtomAbsentFromTheHeadLedger()
    {
        var listed = Entry("source", "listed", "theorem", "1.0", atomizer: AtomizerRegistry.GenericId);
        var ghost = Entry("source", "ghost", "theorem", "2.0", atomizer: AtomizerRegistry.GenericId);
        var baseSnapshot = ReviewSnapshot([listed], quarantined: [], receipted: []);
        var headFiles = ReviewSnapshot([listed], quarantined: [], receipted: []).Entries.ToList();
        headFiles.Add(new RawRepositoryEntry(
            DigestionFormalizationReceipt.PathForAtom("ghost"),
            ImmutableArray.CreateRange(ValidReceipt(ghost))));

        var exception = Assert.Throws<FormatException>(
            () => ReviewEnvelopeCommand.Derive(baseSnapshot, RawRepositorySnapshot.Create(headFiles)));

        Assert.Contains("absent from the head ledger", exception.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("raw_sha256")]
    [InlineData("cas_ref")]
    public void ReviewEnvelopeRejectsAStaleReceiptWhoseFingerprintDoesNotMatchTheLedgerEntry(string mismatchedField)
    {
        // 两个操作数各自独立钉住:只改 raw_sha256、或只改 cas_ref,都必须被拒。
        var atom = Entry("source", "stale", "theorem", "1.0", atomizer: AtomizerRegistry.GenericId);
        var other = Entry("source", "other", "theorem", "2.0", atomizer: AtomizerRegistry.GenericId);
        var baseSnapshot = ReviewSnapshot([atom, other], quarantined: [], receipted: []);
        var headFiles = ReviewSnapshot([atom, other], quarantined: [], receipted: []).Entries.ToList();
        var rawSha = mismatchedField == "raw_sha256" ? other.Atom.Fingerprints.RawSha256 : atom.Atom.Fingerprints.RawSha256;
        var casRef = mismatchedField == "cas_ref" ? other.Atom.Fingerprints.RawSha256 : atom.Atom.Fingerprints.RawSha256;
        var stale = DigestionFormalizationReceipt.Write(new DigestionFormalizationReceipt(
            atom.AtomId,
            "D5/S0/Synthetic/Receipt.stale",
            new DigestionFormalizationSignature("stale", "theorem", "statement-v1"),
            casRef,
            rawSha)).ToArray();
        headFiles.Add(new RawRepositoryEntry(
            DigestionFormalizationReceipt.PathForAtom(atom.AtomId), ImmutableArray.CreateRange(stale)));

        var exception = Assert.Throws<FormatException>(
            () => ReviewEnvelopeCommand.Derive(baseSnapshot, RawRepositorySnapshot.Create(headFiles)));

        Assert.Contains("stale receipt", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ReviewEnvelopeConflictIsATypedOutcomeWithItsOwnExitCode()
    {
        var entry = Entry("source", "both", "theorem", "1.0", atomizer: AtomizerRegistry.GenericId);
        var baseSnapshot = ReviewSnapshot([entry], quarantined: [entry], receipted: []);
        var headSnapshot = ReviewSnapshot([entry], quarantined: [entry], receipted: [entry]);
        var gateway = new RevisionKeyedGateway(new Dictionary<string, RawRepositorySnapshot>(StringComparer.Ordinal)
        {
            ["b"] = baseSnapshot,
            ["h"] = headSnapshot,
        });

        var result = ReviewEnvelopeCommand.Run(gateway, ["--base", "b", "--head", "h"]);

        Assert.False(result.Success);
        Assert.Equal(ReviewEnvelopeCommand.ConflictExitCode, result.ExitCode);
        Assert.StartsWith(ReviewEnvelopeCommand.ConflictMarker + " both", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ReviewEnvelopeValidatesReceiptsThatAlreadyExistedInBase()
    {
        // 既有收据在 head 里被改坏(路径不变、atom_id 改成别的):不是本次新增,仍须拒绝。
        var real = Entry("source", "real", "theorem", "1.0", atomizer: AtomizerRegistry.GenericId);
        var other = Entry("source", "other", "theorem", "2.0", atomizer: AtomizerRegistry.GenericId);
        var baseSnapshot = ReviewSnapshot([real, other], quarantined: [], receipted: [real]);
        var headFiles = ReviewSnapshot([real, other], quarantined: [], receipted: []).Entries.ToList();
        headFiles.Add(new RawRepositoryEntry(
            DigestionFormalizationReceipt.PathForAtom(real.AtomId), ImmutableArray.CreateRange(ValidReceipt(other))));
        headFiles.Add(new RawRepositoryEntry(
            DigestionFormalizationReceipt.PathForAtom(other.AtomId), ImmutableArray.CreateRange(ValidReceipt(other))));

        var exception = Assert.Throws<FormatException>(
            () => ReviewEnvelopeCommand.Derive(baseSnapshot, RawRepositorySnapshot.Create(headFiles)));

        Assert.Contains("path/atom mismatch", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ProductionEnvironmentRoutesReviewEnvelopeToTheCommand()
    {
        var entry = Entry("source", "prod-routed", "theorem", "1.0", atomizer: AtomizerRegistry.GenericId);
        var baseSnapshot = ReviewSnapshot([entry], quarantined: [], receipted: []);
        var headSnapshot = ReviewSnapshot([entry], quarantined: [], receipted: [entry]);
        var environment = new ProductionCliEnvironment(
            "/repo",
            new RevisionKeyedGateway(new Dictionary<string, RawRepositorySnapshot>(StringComparer.Ordinal)
            {
                ["b"] = baseSnapshot,
                ["h"] = headSnapshot,
            }),
            new FakeLeanReportSource(CurrentLeanReport([entry])),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.ReviewEnvelope(["--base", "b", "--head", "h"]);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal(ReviewEnvelopeCommand.Schema, json.RootElement.GetProperty("schema").GetString());
        Assert.Equal("prod-routed", Assert.Single(json.RootElement.GetProperty("deposited").EnumerateArray()).GetProperty("atom_id").GetString());
    }

    [Fact]
    public void ReviewEnvelopeRejectsMalformedReceiptJsonWithTheInvalidMarker()
    {
        var entry = Entry("source", "malformed", "theorem", "1.0", atomizer: AtomizerRegistry.GenericId);
        var baseSnapshot = ReviewSnapshot([entry], quarantined: [], receipted: []);
        var headFiles = ReviewSnapshot([entry], quarantined: [], receipted: []).Entries.ToList();
        headFiles.Add(new RawRepositoryEntry(
            DigestionFormalizationReceipt.PathForAtom(entry.AtomId),
            ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("{\"atom_id\": \"malformed\", "))));
        var gateway = new RevisionKeyedGateway(new Dictionary<string, RawRepositorySnapshot>(StringComparer.Ordinal)
        {
            ["b"] = baseSnapshot,
            ["h"] = RawRepositorySnapshot.Create(headFiles),
        });

        var result = ReviewEnvelopeCommand.Run(gateway, ["--base", "b", "--head", "h"]);

        Assert.False(result.Success);
        Assert.StartsWith(ReviewEnvelopeCommand.InvalidMarker, result.Error, StringComparison.Ordinal);
        Assert.NotEqual(ReviewEnvelopeCommand.ConflictExitCode, result.ExitCode);
    }

    [Fact]
    public void ReviewEnvelopeConflictViaCoverageGidsIsTheSameTypedOutcome()
    {
        // 第二个抛出点:隔离 + coverage_gids(机器形式陈述)——同一典型结果,exit 3。
        var entry = Entry("source", "covered", "theorem", "1.0", coverageGids: ["D5/S0/Synthetic/Receipt.covered"], atomizer: AtomizerRegistry.GenericId);
        var baseSnapshot = ReviewSnapshot([entry], quarantined: [], receipted: []);
        var headSnapshot = ReviewSnapshot([entry], quarantined: [entry], receipted: []);
        var gateway = new RevisionKeyedGateway(new Dictionary<string, RawRepositorySnapshot>(StringComparer.Ordinal)
        {
            ["b"] = baseSnapshot,
            ["h"] = headSnapshot,
        });

        var result = ReviewEnvelopeCommand.Run(gateway, ["--base", "b", "--head", "h"]);

        Assert.Equal(ReviewEnvelopeCommand.ConflictExitCode, result.ExitCode);
        Assert.StartsWith(ReviewEnvelopeCommand.ConflictMarker + " covered", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ReviewEnvelopeVerbIsRegistered()
    {
        Assert.Contains("review-envelope", CliApplication.ImplementedCommands);
    }

    // 合成快照:规则文件(Minimal)、账本(按 quarantined 集合给条目加隔离块)、源文与 CAS、以及 receipted
    // 集合的收据。两棵快照的差别只在 quarantined / receipted 两个集合,派生规则由此可被逐条钉住。
    private static byte[] ExtendedReceipt(EntryFixture entry, params string[] hostedGids) =>
        DigestionFormalizationReceipt.Write(new DigestionFormalizationReceipt(
            entry.AtomId,
            "D5/S0/Synthetic/Receipt." + entry.AtomId.Replace('-', '_'),
            new DigestionFormalizationSignature(entry.AtomId.Replace('-', '_'), "theorem", "statement-v1"),
            entry.Atom.Fingerprints.RawSha256,
            entry.Atom.Fingerprints.RawSha256,
            ImmutableArray.CreateRange(hostedGids.Select(static gid => new DigestionFormalizationExtension(
                gid,
                new DigestionFormalizationSignature(gid.Replace('/', '_').Replace('.', '_'), "theorem", "statement-v1")))))).ToArray();

    private static RawRepositorySnapshot WithReceiptBytes(RawRepositorySnapshot snapshot, EntryFixture entry, byte[] receipt)
    {
        var files = snapshot.Entries
            .Where(file => file.Path != DigestionFormalizationReceipt.PathForAtom(entry.AtomId))
            .ToList();
        files.Add(new RawRepositoryEntry(DigestionFormalizationReceipt.PathForAtom(entry.AtomId), ImmutableArray.CreateRange(receipt)));
        return RawRepositorySnapshot.Create(files);
    }

    [Fact]
    public void ReviewEnvelopeReportsAReceiptThatOnlyGainedHostedExtensionsAsExtended()
    {
        var entry = Entry("source", "hosted", "theorem", "1.0", atomizer: AtomizerRegistry.GenericId);
        var baseSnapshot = ReviewSnapshot([entry], quarantined: [], receipted: [entry]);
        var headSnapshot = WithReceiptBytes(baseSnapshot, entry, ExtendedReceipt(entry, "D5/S0/Synthetic/Receipt.hosted_more"));
        var gateway = new RevisionKeyedGateway(new Dictionary<string, RawRepositorySnapshot>(StringComparer.Ordinal)
        {
            ["b"] = baseSnapshot,
            ["h"] = headSnapshot,
        });

        var result = ReviewEnvelopeCommand.Run(gateway, ["--base", "b", "--head", "h"]);

        Assert.True(result.Success, result.Error);
        using var document = JsonDocument.Parse(result.Output);
        Assert.Empty(document.RootElement.GetProperty("deposited").EnumerateArray());
        Assert.Empty(document.RootElement.GetProperty("ejected").EnumerateArray());
        var extended = Assert.Single(document.RootElement.GetProperty("extended").EnumerateArray());
        Assert.Equal(entry.AtomId, extended.GetProperty("atom_id").GetString());
        Assert.Equal(
            "D5/S0/Synthetic/Receipt.hosted_more",
            Assert.Single(extended.GetProperty("added_gids").EnumerateArray()).GetString());
    }

    [Fact]
    public void ReviewEnvelopeDoesNotReportAnUnchangedReceiptAsExtended()
    {
        var kept = Entry("source", "kept", "theorem", "1.0", atomizer: AtomizerRegistry.GenericId);
        var fresh = Entry("source", "fresh", "theorem", "2.0", atomizer: AtomizerRegistry.GenericId);
        var baseSnapshot = ReviewSnapshot([kept, fresh], quarantined: [], receipted: [kept]);
        var headSnapshot = ReviewSnapshot([kept, fresh], quarantined: [], receipted: [kept, fresh]);

        var derivation = ReviewEnvelopeCommand.Derive(baseSnapshot, headSnapshot);

        Assert.Empty(derivation.ExtendedAtoms);
        Assert.Equal(fresh.AtomId, Assert.Single(derivation.DepositedAtoms).AtomId);
    }

    [Theory]
    [InlineData("extension-removed")]
    [InlineData("primary-gid-rewritten")]
    public void ReviewEnvelopeRejectsAnExistingReceiptThatWasRewritten(string rewrite)
    {
        var entry = Entry("source", "rewritten", "theorem", "1.0", atomizer: AtomizerRegistry.GenericId);
        var plain = ReviewSnapshot([entry], quarantined: [], receipted: [entry]);
        var withExtension = WithReceiptBytes(plain, entry, ExtendedReceipt(entry, "D5/S0/Synthetic/Receipt.rewritten_ext"));
        var otherPrimary = WithReceiptBytes(plain, entry, DigestionFormalizationReceipt.Write(new DigestionFormalizationReceipt(
            entry.AtomId,
            "D5/S0/Synthetic/Receipt.other_primary",
            new DigestionFormalizationSignature("other_primary", "theorem", "statement-v1"),
            entry.Atom.Fingerprints.RawSha256,
            entry.Atom.Fingerprints.RawSha256)).ToArray());
        var (baseSnapshot, headSnapshot) = rewrite == "extension-removed" ? (withExtension, plain) : (plain, otherPrimary);

        var exception = Assert.ThrowsAny<FormatException>(
            () => ReviewEnvelopeCommand.Derive(baseSnapshot, headSnapshot));

        Assert.StartsWith("rewritten receipt: ", exception.Message, StringComparison.Ordinal);
    }

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
