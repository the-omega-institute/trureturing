using System.Collections.Immutable;
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
    [InlineData("CHAIN_PARENT")]
    [InlineData("CONTEXT_MISMATCH", "previous")]
    [InlineData("CONTEXT_MISMATCH", "next")]
    [InlineData("CONTEXT_MISMATCH", "previous-boundary")]
    [InlineData("CONTEXT_MISMATCH", "next-boundary")]
    [InlineData("ATOMIZER_NONE")]
    [InlineData("SOURCE_MISSING")]
    [InlineData("OCCURRENCE_MISSING")]
    [InlineData("OCCURRENCE_AMBIGUOUS")]
    [InlineData("REQUEST_KEYS_INVALID")]
    [InlineData("REQUEST_VALUE_BLANK")]
    [InlineData("REQUEST_TOML_INVALID")]
    [InlineData("REQUEST_ENCODING_INVALID")]
    [InlineData("NONPROPOSITIONAL_ABSENT")]
    public void SettleRejectsWrongStateConflictsAndNonAdjacentContextWithoutWrites(string code, string side = "previous")
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
            "CHAIN_PARENT" => target with { Receipts = target.Receipts with { ChainAtoms = [new string('f', 64)] } },
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
            "CONTEXT_MISMATCH" => request.Replace(
                $"{(side.StartsWith("previous", StringComparison.Ordinal) ? "previous" : "next")}_atom_id = '"
                    + (side.StartsWith("previous", StringComparison.Ordinal)
                        ? AtomContextFixture.Id(fixture.Atomized.Claims[0]) : AtomContextFixture.Id(fixture.Atomized.Claims[2])) + "'",
                $"{(side.StartsWith("previous", StringComparison.Ordinal) ? "previous" : "next")}_atom_id = '"
                    + (side.EndsWith("boundary", StringComparison.Ordinal) ? "source-boundary" : new string('f', 64)) + "'",
                StringComparison.Ordinal),
            "REQUEST_KEYS_INVALID" => request + "extra = 'value'\n",
            "REQUEST_VALUE_BLANK" => request.Replace(Reason, "   ", StringComparison.Ordinal),
            "REQUEST_TOML_INVALID" => "atom_id = [\n",
            "REQUEST_ENCODING_INVALID" => request.Replace("\n", "\r\n", StringComparison.Ordinal),
            _ => request,
        };
        var raw = code == "SOURCE_MISSING" ? fixture.RawSnapshot(false) : fixture.RawSnapshot();
        using var temporary = new TemporaryDirectory();
        WriteFiles(temporary.Path, raw);
        var before = Image(temporary);
        var applyCalls = 0;
        var result = Run(temporary.Path, raw, request,
            code == "NONPROPOSITIONAL_ABSENT" ? ["--clear", target.AtomId, "--base", "baseline"] : null,
            (root, current, updates) => { applyCalls++; IngestCommand.ApplyLedgerUpdatesAtomically(root, current, updates); });
        Assert.False(result.Success);
        if (code == "CONTEXT_MISMATCH") output.WriteLine(result.Error.TrimEnd());
        Assert.StartsWith("SETTLE_INVALID " + code, result.Error, StringComparison.Ordinal);
        Assert.Equal(before, Image(temporary));
        Assert.Equal(0, applyCalls);
    }

    [Theory]
    [InlineData("open", false, false)]
    [InlineData("absorbed", false, false)]
    [InlineData("nonpropositional", false, false)]
    [InlineData("nonpropositional", false, true)]
    [InlineData("nonpropositional", true, false)]
    public void SettleRejectsChainParentsBeforeContextLookupWithoutWrites(string childState, bool clear, bool sourceMissing)
    {
        var fixture = AtomContextFixture.Create(AtomContextFixture.ListClaims);
        var id = AtomContextFixture.Id(fixture.Atomized.Claims[1]);
        var request = Request(fixture, id);
        fixture = AtomContextFixture.Create(AtomContextFixture.ListClaims, true);
        var parent = fixture.Ledger.RequireDigestionEntries().Single(entry => entry.AtomId == id);
        fixture = fixture.WithEntries(fixture.Ledger.RequireDigestionEntries().Select(entry =>
        {
            if (clear && entry == parent) return Settled(entry);
            if (!parent.Receipts.ChainAtoms.Contains(entry.AtomId, StringComparer.Ordinal)) return entry;
            return childState switch
            {
                "nonpropositional" => Settled(entry),
                "absorbed" => entry with
                {
                    Coverage = [new("D5/S0/Carrier/Probe", null)],
                    ProjectedStatus = new(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
                },
                _ => entry,
            };
        }));
        var raw = fixture.RawSnapshot(!sourceMissing);
        using var temporary = new TemporaryDirectory();
        WriteFiles(temporary.Path, raw);
        var before = Image(temporary);
        var applyCalls = 0;
        var result = Run(temporary.Path, raw, request, clear ? ["--clear", id, "--base", "baseline"] : null,
            apply: (_, _, _) => applyCalls++);
        Assert.False(result.Success);
        Assert.Equal($"SETTLE_INVALID CHAIN_PARENT atom_id={id}\n", result.Error);
        Assert.Equal(0, applyCalls);
        Assert.Equal(before, Image(temporary));
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
        var before = Image(temporary);
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
        if (ioError)
        {
            Assert.Equal("SETTLE_INVALID INFRASTRUCTURE simulated write error after rename\n", result.Error);
            Assert.Equal(before, Image(temporary));
        }
        else
        {
            Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(temporary.Path, PathFor(target))));
            var loaded = BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries().Single(entry => entry.AtomId == id);
            Assert.Equal(State, StateName(loaded.ProjectedStatus));
            Assert.Equal($"SETTLED_NONPROPOSITIONAL atom_id={id} path={PathFor(target, State)}\n", result.Output);
            var after = ReadFiles(temporary);
            var replay = Run(temporary.Path, after, Request(fixture, id));
            Assert.StartsWith("SETTLE_INVALID NOT_RESIDUAL_OPEN", replay.Error, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void SettleReportsConcurrentLedgerChangeWithoutOverwritingBytes()
    {
        var fixture = AtomContextFixture.Create();
        var id = AtomContextFixture.Id(fixture.Atomized.Claims[1]);
        var target = fixture.Ledger.RequireDigestionEntries().Single(entry => entry.AtomId == id);
        var raw = fixture.RawSnapshot();
        using var temporary = new TemporaryDirectory();
        WriteFiles(temporary.Path, raw);
        TemporaryFileSystem.File.AppendAllText(Path.Combine(temporary.Path, PathFor(target)), "\n", Encoding.UTF8);
        var before = Image(temporary);
        var applyCalls = 0;
        var commitCalls = 0;
        var result = Run(temporary.Path, raw, Request(fixture, id), apply: (root, current, updates) =>
        {
            applyCalls++;
            IngestCommand.ApplyLedgerUpdatesAtomically(root, current, updates, (pending, destination) =>
            {
                commitCalls++;
                File.Move(pending, destination, true);
            });
        });
        Assert.False(result.Success);
        Assert.StartsWith("SETTLE_INVALID INFRASTRUCTURE ledger changed under us ", result.Error, StringComparison.Ordinal);
        Assert.Equal(1, applyCalls);
        Assert.Equal(0, commitCalls);
        Assert.Equal(before, Image(temporary));
    }

    [Fact]
    public void SettleReportsMalformedLedgerWithoutWrites()
    {
        var fixture = AtomContextFixture.Create();
        var id = AtomContextFixture.Id(fixture.Atomized.Claims[1]);
        var target = fixture.Ledger.RequireDigestionEntries().Single(entry => entry.AtomId == id);
        var raw = RawRepositorySnapshot.Create(fixture.RawSnapshot().Entries.Select(entry =>
            entry.Path == PathFor(target) ? RawRepositoryEntry.FromText(entry.Path, "receipts: []\n") : entry));
        using var temporary = new TemporaryDirectory();
        WriteFiles(temporary.Path, raw);
        var before = Image(temporary);
        var applyCalls = 0;
        var result = Run(temporary.Path, raw, Request(fixture, id), apply: (_, _, _) => applyCalls++);
        Assert.False(result.Success);
        Assert.StartsWith("SETTLE_INVALID INFRASTRUCTURE ", result.Error, StringComparison.Ordinal);
        Assert.Equal(0, applyCalls);
        Assert.Equal(before, Image(temporary));
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
            TemporaryFileSystem.File.ReadAllBytes(Path.Combine(temporary.Path, PathFor(target))));
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(temporary.Path, PathFor(target, State))));
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
        var before = Image(temporary);
        var calls = 0;
        var result = Run(temporary.Path, raw, Request(fixture, target.AtomId), apply: (_, _, _) => calls++);
        Assert.False(result.Success);
        Assert.StartsWith("SETTLE_INVALID NOT_RESIDUAL_OPEN", result.Error, StringComparison.Ordinal);
        Assert.Equal(0, calls);
        Assert.Equal(before, Image(temporary));
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
        var before = Image(temporary);
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
        Assert.Equal(before, Image(temporary));
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
    [InlineData(false, false, false)]
    [InlineData(true, false, false)]
    [InlineData(false, true, false)]
    [InlineData(true, true, false)]
    [InlineData(false, false, true)]
    [InlineData(true, false, true)]
    [InlineData(false, true, true)]
    [InlineData(true, true, true)]
    public void SettleAlignRequiredIsPrintedOnlyForCoveredAncestors(bool covered, bool clear, bool transitive)
    {
        var fixture = AtomContextFixture.Create(AtomContextFixture.ListClaims, true);
        var parent = fixture.Ledger.RequireDigestionEntries().Single(entry => !entry.Receipts.ChainAtoms.IsEmpty);
        var id = parent.Receipts.ChainAtoms[1];
        var ancestor = AtomContextFixture.Create("## Ancestor\n\nAncestor.\n").Ledger.RequireDigestionEntries().Single();
        ancestor = ancestor with { Receipts = ancestor.Receipts with { ChainAtoms = [parent.AtomId] } };
        var coveredId = transitive ? ancestor.AtomId : parent.AtomId;
        var entries = fixture.Ledger.RequireDigestionEntries().AsEnumerable();
        if (transitive) entries = entries.Append(ancestor);
        fixture = fixture.WithEntries(entries.Select(entry =>
        {
            if (clear && parent.Receipts.ChainAtoms.Contains(entry.AtomId, StringComparer.Ordinal)) entry = Settled(entry);
            return entry.AtomId == coveredId && covered ? entry with
            {
                Coverage = [new("D5/S0/Carrier/Probe", null)],
                ProjectedStatus = clear ? new(DigestionMigrationState.Absorbed, DigestionTruthState.Closed) : entry.ProjectedStatus,
            } : entry;
        }));
        using var temporary = new TemporaryDirectory();
        WriteFiles(temporary.Path, fixture.RawSnapshot());
        var result = Run(temporary.Path, fixture.RawSnapshot(), Request(fixture, id),
            clear ? ["--clear", id, "--base", "baseline"] : null);
        Assert.True(result.Success, result.Error);
        var lines = result.Output.Split('\n', StringSplitOptions.RemoveEmptyEntries);
        Assert.Equal(covered ? 2 : 1, lines.Length);
        if (covered) Assert.Equal("SETTLE_ALIGN_REQUIRED ancestors=" + coveredId, lines[1]);
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
        return Assert.IsType<CommandResult>(SettleAtomCommand.Run(root,
            new FakeRepositoryGateway(RawChangeSet.Create([]), raw, raw),
            arguments ?? ["--request", "request.toml", "--base", "baseline"],
            writer ?? BackfillInventoryWriter.WriteAtom,
            (_, _) => [.. Encoding.UTF8.GetBytes(request)],
            apply ?? ((directory, current, updates) => IngestCommand.ApplyLedgerUpdatesAtomically(directory, current, updates))));
    }

    internal static void WriteFiles(string root, RawRepositorySnapshot raw)
    {
        foreach (var entry in raw.Entries)
        {
            var path = Path.Combine(root, entry.Path);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            TemporaryFileSystem.File.WriteAllBytes(path, entry.Bytes.ToArray());
        }
    }

    internal static RawRepositorySnapshot ReadFiles(TemporaryDirectory temporary) => RawRepositorySnapshot.Create(
        Directory.EnumerateFiles(temporary.Path, "*", SearchOption.AllDirectories).Select(path =>
            new RawRepositoryEntry(Path.GetRelativePath(temporary.Path, path).Replace('\\', '/'), [.. TemporaryFileSystem.File.ReadAllBytes(path)])));

    internal static string Image(TemporaryDirectory temporary) => string.Join('\n', ReadFiles(temporary).Entries
        .OrderBy(static entry => entry.Path, StringComparer.Ordinal)
        .Select(static entry => entry.Path + ":" + Convert.ToHexString(entry.Bytes.AsSpan())));
}
