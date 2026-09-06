using System.Collections.Immutable;
using System.Reflection;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.NonpropositionalTestSupport;

namespace StrataLint.Tests;

public sealed class SettleAtomCommandTests(Xunit.Abstractions.ITestOutputHelper output)
{
    [Theory]
    [InlineData("ATOM_ABSENT")]
    [InlineData("ATOM_AMBIGUOUS")]
    [InlineData("NOT_RESIDUAL_OPEN")]
    [InlineData("COVERAGE_PRESENT")]
    [InlineData("QUARANTINE_PRESENT")]
    [InlineData("COVER_DISPOSITION_PRESENT")]
    [InlineData("UNRESOLVED_SUBITEMS_PRESENT")]
    [InlineData("CHAIN_OPEN")]
    [InlineData("CONTEXT_MISMATCH")]
    [InlineData("ATOMIZER_NONE")]
    [InlineData("SOURCE_MISSING")]
    [InlineData("OCCURRENCE_MISSING")]
    [InlineData("OCCURRENCE_AMBIGUOUS")]
    [InlineData("REQUEST_KEYS_INVALID")]
    [InlineData("REQUEST_VALUE_BLANK")]
    [InlineData("REQUEST_TOML_INVALID")]
    [InlineData("REQUEST_ENCODING_INVALID")]
    [InlineData("NONPROPOSITIONAL_ABSENT")]
    public void SettleRejectsWrongStateConflictsAndNonAdjacentContextWithoutWrites(string code)
    {
        var fixture = AtomContextFixture.Create();
        var target = fixture.Ledger.RequireDigestionEntries().Single(entry =>
            entry.AtomId == AtomContextFixture.Id(fixture.Atomized.Claims[1]));
        var request = Request(fixture, target.AtomId);
        var updated = code switch
        {
            "NOT_RESIDUAL_OPEN" => target with { ProjectedStatus = new(DigestionMigrationState.Partial, DigestionTruthState.Open) },
            "COVERAGE_PRESENT" => target with { Coverage = [new("D5/S0/Carrier/Probe", null)] },
            "QUARANTINE_PRESENT" => target with { Receipts = target.Receipts with { Quarantine = new("blocked", "supply witness", "missing-prerequisite") } },
            "COVER_DISPOSITION_PRESENT" => target with { Receipts = target.Receipts with { CoverDisposition = new(new(DigestionMigrationState.Partial, DigestionTruthState.Closed), ["D5/S0/Carrier/Probe"], []) } },
            "UNRESOLVED_SUBITEMS_PRESENT" => target with { Receipts = target.Receipts with { UnresolvedSubitems = ["live obligation"] } },
            "CHAIN_OPEN" => target with { Receipts = target.Receipts with { ChainAtoms = [new string('f', 64)] } },
            "ATOMIZER_NONE" => target with { Atomizer = AtomizerRegistry.NoAtomizerId },
            _ => target,
        };
        fixture = fixture.WithEntries(fixture.Ledger.RequireDigestionEntries().Select(entry => entry == target ? updated : entry));
        if (code == "ATOMIZER_NONE") fixture = fixture with { Ledger = fixture.Ledger.WithDigestionSources([
            fixture.Ledger.RequireDigestionSources().Single() with { Atomizer = AtomizerRegistry.NoAtomizerId }]) };
        if (code == "ATOM_AMBIGUOUS")
        {
            var source = fixture.Ledger.RequireDigestionSources().Single();
            fixture = fixture with { Ledger = fixture.Ledger.WithDigestionSources([source,
                source with { SourceId = "second", Entries = [target with { SourceId = "second" }] }]) };
        }
        if (code == "OCCURRENCE_MISSING") fixture = fixture with { SourceBytes = Encoding.UTF8.GetBytes("Other text.\n") };
        if (code == "OCCURRENCE_AMBIGUOUS") fixture = fixture with { SourceBytes = fixture.SourceBytes.Concat(fixture.SourceBytes).ToArray() };
        request = code switch
        {
            "ATOM_ABSENT" => request.Replace(target.AtomId, new string('f', 64), StringComparison.Ordinal),
            "CONTEXT_MISMATCH" => request.Replace(DigestionAtomContextProjection.Resolve(fixture.Snapshot(), fixture.Ledger, target.AtomId).Previous!.Value.AtomId,
                    "source-boundary", StringComparison.Ordinal),
            "REQUEST_KEYS_INVALID" => request + "extra = 'value'\n",
            "REQUEST_VALUE_BLANK" => request.Replace(Reason, "   ", StringComparison.Ordinal),
            "REQUEST_TOML_INVALID" => "atom_id = [\n",
            "REQUEST_ENCODING_INVALID" => request.Replace("\n", "\r\n", StringComparison.Ordinal),
            _ => request,
        };
        var raw = code == "SOURCE_MISSING" ? fixture.RawSnapshot(false) : fixture.RawSnapshot();
        using var temporary = new TemporaryDirectory();
        WriteFiles(temporary.Path, raw);
        var before = Image(temporary.Path);
        var applyCalls = 0;
        var result = Run(temporary.Path, raw, request,
            code == "NONPROPOSITIONAL_ABSENT" ? ["--clear", target.AtomId, "--base", "baseline"] : null,
            (root, current, updates) => { applyCalls++; IngestCommand.ApplyLedgerUpdatesAtomically(root, current, updates); });
        Assert.False(result.Success);
        if (code == "CONTEXT_MISMATCH") output.WriteLine(result.Error.TrimEnd());
        Assert.StartsWith("SETTLE_INVALID " + code, result.Error, StringComparison.Ordinal);
        Assert.Equal(before, Image(temporary.Path));
        Assert.Equal(0, applyCalls);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SettleMovesShardAtomicallyAndRollsBackOnIoError(bool ioError)
    {
        var fixture = AtomContextFixture.Create();
        var id = AtomContextFixture.Id(fixture.Atomized.Claims[1]);
        var target = fixture.Ledger.RequireDigestionEntries().Single(entry => entry.AtomId == id);
        var raw = fixture.RawSnapshot();
        using var temporary = new TemporaryDirectory();
        WriteFiles(temporary.Path, raw);
        var before = Image(temporary.Path);
        var applyCalls = 0;
        var result = Run(temporary.Path, raw, Request(fixture, id), null, (root, current, updates) =>
        {
            applyCalls++;
            Assert.Equal(2, updates.Length);
            Assert.Contains(updates, update => update.Path == PathFor(target) && update.Bytes is null);
            Assert.Contains(updates, update => update.Path == PathFor(target, State) && update.Bytes is not null);
            IngestCommand.ApplyLedgerUpdatesAtomically(root, current, updates, (pending, output) =>
            {
                File.Move(pending, output, true);
                if (ioError) throw new IOException("simulated write error after rename");
            });
        });
        Assert.Equal(1, applyCalls);
        Assert.Equal(!ioError, result.Success);
        if (!ioError) output.WriteLine(result.Output.TrimEnd());
        if (ioError) Assert.Equal(before, Image(temporary.Path));
        else
        {
            Assert.False(File.Exists(Path.Combine(temporary.Path, PathFor(target))));
            var loaded = BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries().Single(entry => entry.AtomId == id);
            Assert.Equal(State, StateName(loaded.ProjectedStatus));
            Assert.Equal($"SETTLED_NONPROPOSITIONAL atom_id={id} path={PathFor(target, State)}\n", result.Output);
            var after = ReadFiles(temporary.Path);
            var replay = Run(temporary.Path, after, Request(fixture, id));
            Assert.StartsWith("SETTLE_INVALID NOT_RESIDUAL_OPEN", replay.Error, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void SettleClearRestoresResidualOpen()
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var target = fixture.Ledger.RequireDigestionEntries().Single();
        fixture = fixture.WithEntries([Settled(target)]);
        using var temporary = new TemporaryDirectory();
        var raw = fixture.RawSnapshot();
        WriteFiles(temporary.Path, raw);
        var result = Run(temporary.Path, raw, "", ["--clear", target.AtomId, "--base", "baseline"]);
        Assert.True(result.Success, result.Error);
        Assert.Equal($"SETTLE_CLEARED atom_id={target.AtomId} path={PathFor(target)}\n", result.Output);
        Assert.Equal(BackfillInventoryWriter.WriteAtom(target).ToArray(),
            File.ReadAllBytes(Path.Combine(temporary.Path, PathFor(target))));
        Assert.False(File.Exists(Path.Combine(temporary.Path, PathFor(target, State))));
    }

    [Fact]
    public void SettleRejectsReceiptReplacementInResidualDirectoryWithoutWrites()
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var target = fixture.Ledger.RequireDigestionEntries().Single();
        fixture = fixture.WithEntries([Settled(target) with { ProjectedStatus = target.ProjectedStatus }]);
        using var temporary = new TemporaryDirectory();
        var raw = fixture.RawSnapshot();
        WriteFiles(temporary.Path, raw);
        var before = Image(temporary.Path);
        var calls = 0;
        var result = Run(temporary.Path, raw, Request(fixture, target.AtomId), apply: (_, _, _) => calls++);
        Assert.False(result.Success);
        Assert.StartsWith("SETTLE_INVALID NOT_RESIDUAL_OPEN", result.Error, StringComparison.Ordinal);
        Assert.Equal(0, calls);
        Assert.Equal(before, Image(temporary.Path));
    }

    [Fact]
    public void SettleVerifiesSourceBoundariesAndSerializesNull()
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var target = fixture.Ledger.RequireDigestionEntries().Single();
        using var temporary = new TemporaryDirectory();
        WriteFiles(temporary.Path, fixture.RawSnapshot());
        var result = Run(temporary.Path, fixture.RawSnapshot(), Request(fixture, target.AtomId));
        Assert.True(result.Success, result.Error);
        var receipt = BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries().Single().Receipts.Nonpropositional;
        Assert.NotNull(receipt);
        Assert.Null(receipt.PreviousAtomId);
        Assert.Null(receipt.NextAtomId);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SettleRejectsInvalidOrUnstableSerializationWithoutWrites(bool unstable)
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var target = fixture.Ledger.RequireDigestionEntries().Single();
        using var temporary = new TemporaryDirectory();
        var raw = fixture.RawSnapshot();
        WriteFiles(temporary.Path, raw);
        var before = Image(temporary.Path);
        var calls = 0;
        var serializations = 0;
        ImmutableArray<byte> Writer(DigestionLedgerEntry entry)
        {
            serializations++;
            return unstable ? [.. BackfillInventoryWriter.WriteAtom(entry), .. Encoding.UTF8.GetBytes(new string('\n', serializations))]
                : [.. Encoding.UTF8.GetBytes("receipts: []\n")];
        }
        var result = Run(temporary.Path, raw, Request(fixture, target.AtomId), apply: (_, _, _) => calls++, writer: Writer);
        Assert.False(result.Success);
        Assert.StartsWith("SETTLE_INVALID ROUND_TRIP_FAILED", result.Error, StringComparison.Ordinal);
        Assert.Equal(0, calls);
        Assert.Equal(before, Image(temporary.Path));
    }

    [Fact]
    public void SettleRejectsReplace()
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var result = Run("/synthetic", fixture.RawSnapshot(), "",
            ["--request", "request.toml", "--base", "baseline", "--replace"]);
        Assert.False(result.Success);
        Assert.StartsWith("SETTLE_INVALID ARGUMENTS_INVALID", result.Error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SettleAlignRequiredIsPrintedOnlyForCoveredAncestors(bool covered)
    {
        var fixture = AtomContextFixture.Create(AtomContextFixture.ListClaims, true);
        var parent = fixture.Ledger.RequireDigestionEntries().Single(entry => !entry.Receipts.ChainAtoms.IsEmpty);
        var id = parent.Receipts.ChainAtoms[1];
        fixture = fixture.WithEntries(fixture.Ledger.RequireDigestionEntries().Select(entry =>
            entry == parent && covered ? entry with { Coverage = [new("D5/S0/Carrier/Probe", null)] } : entry));
        using var temporary = new TemporaryDirectory();
        WriteFiles(temporary.Path, fixture.RawSnapshot());
        var result = Run(temporary.Path, fixture.RawSnapshot(), Request(fixture, id));
        Assert.True(result.Success, result.Error);
        Assert.Equal(covered, result.Output.Contains("SETTLE_ALIGN_REQUIRED ancestors=" + parent.AtomId, StringComparison.Ordinal));
    }

    [Fact]
    public void QuarantineRefusesNonpropositionalReceipt()
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var target = Settled(fixture.Ledger.RequireDigestionEntries().Single());
        fixture = fixture.WithEntries([target]);
        var raw = fixture.RawSnapshot();
        var result = QuarantineAtomCommand.Run("/synthetic", new FakeRepositoryGateway(RawChangeSet.Create([]), raw, raw),
            ["--clear", target.AtomId, "--base", "baseline"]);
        Assert.False(result.Success);
        Assert.StartsWith("QUARANTINE_INVALID NONPROPOSITIONAL_PRESENT", result.Error, StringComparison.Ordinal);
    }

    internal static string Request(AtomContextFixture fixture, string id)
    {
        var context = DigestionAtomContextProjection.Resolve(fixture.Snapshot(), fixture.Ledger, id);
        return $"atom_id = '{id}'\njustification = '{Reason}'\n"
            + $"previous_atom_id = '{context.Previous?.AtomId ?? "source-boundary"}'\n"
            + $"next_atom_id = '{context.Next?.AtomId ?? "source-boundary"}'\n";
    }

    internal static CommandResult Run(string root, RawRepositorySnapshot raw, string request,
        IReadOnlyList<string>? arguments = null,
        Action<string, RawRepositorySnapshot, ImmutableArray<IngestCommand.LedgerUpdate>>? apply = null,
        Func<DigestionLedgerEntry, ImmutableArray<byte>>? writer = null)
    {
        var type = typeof(CliApplication).Assembly.GetType("StrataLint.Cli.SettleAtomCommand");
        Assert.NotNull(type);
        var method = Assert.Single(type.GetMethods(BindingFlags.Static | BindingFlags.NonPublic),
            method => method.Name == "Run" && method.GetParameters().Length == 6);
        return Assert.IsType<CommandResult>(method.Invoke(null, [root,
            new FakeRepositoryGateway(RawChangeSet.Create([]), raw, raw),
            arguments ?? ["--request", "request.toml", "--base", "baseline"],
            writer ?? BackfillInventoryWriter.WriteAtom,
            (Func<string, string, ImmutableArray<byte>>)((_, _) => [.. Encoding.UTF8.GetBytes(request)]),
            apply ?? ((directory, current, updates) => IngestCommand.ApplyLedgerUpdatesAtomically(directory, current, updates))]));
    }

    internal static void WriteFiles(string root, RawRepositorySnapshot raw)
    {
        foreach (var entry in raw.Entries)
        {
            var path = Path.Combine(root, entry.Path);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllBytes(path, entry.Bytes.AsSpan());
        }
    }

    internal static RawRepositorySnapshot ReadFiles(string root) => RawRepositorySnapshot.Create(
        Directory.EnumerateFiles(root, "*", SearchOption.AllDirectories).Select(path =>
            new RawRepositoryEntry(Path.GetRelativePath(root, path).Replace('\\', '/'), [.. File.ReadAllBytes(path)])));

    internal static string Image(string root) => string.Join('\n', ReadFiles(root).Entries
        .OrderBy(static entry => entry.Path, StringComparer.Ordinal)
        .Select(static entry => entry.Path + ":" + Convert.ToHexString(entry.Bytes.AsSpan())));
}
