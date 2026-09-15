using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.SettleAtomCommandTests;
using static StrataLint.Tests.UpstreamProbeVerifierTests;

namespace StrataLint.Tests;

public sealed partial class SettleUpstreamCommandTests
{
    [Theory]
    [InlineData("atom_id")]
    [InlineData("justification")]
    [InlineData("declarations")]
    [InlineData("probe")]
    [InlineData("previous_atom_id")]
    [InlineData("next_atom_id")]
    public void MissingAndMalformedRequestKeysAreRejected(string key)
    {
        using var f = new Fixture();
        var lines = f.Request.Split('\n', StringSplitOptions.RemoveEmptyEntries);
        f.Reject("REQUEST_KEYS_INVALID", string.Join('\n', lines.Where(line => !line.StartsWith(key + " =", StringComparison.Ordinal))) + "\n");
        f.Reject("ARGUMENTS_INVALID", string.Join('\n', lines.Select(line => line.StartsWith(key + " =", StringComparison.Ordinal) ? key + " = 17" : line)) + "\n");
    }

    [Theory]
    [InlineData("extra = 'x'\n", "REQUEST_KEYS_INVALID")]
    [InlineData("occurrence_index = 1\n", "REQUEST_KEYS_INVALID")]
    public void ExtraKeysAreRejected(string extra, string code)
    {
        using var f = new Fixture();
        f.Reject(code, f.Request + extra);
    }

    [Theory]
    [InlineData("atom_id", "''")]
    [InlineData("atom_id", "'abc'")]
    [InlineData("justification", "' '")]
    [InlineData("declarations", "[]")]
    [InlineData("declarations", "['Nat.add_comm', 1]")]
    [InlineData("declarations", "['Nat.add_comm', 'Nat.add_comm']")]
    [InlineData("declarations", "['Nat.add_comm\\n#eval bad']")]
    [InlineData("previous_atom_id", "'SOURCE-BOUNDARY'")]
    [InlineData("next_atom_id", "'bad'")]
    public void InvalidRequestValuesAreRejected(string key, string value)
    {
        using var f = new Fixture();
        f.Reject("ARGUMENTS_INVALID", string.Join('\n', f.Request.Split('\n').Select(line => line.StartsWith(key + " =", StringComparison.Ordinal) ? key + " = " + value : line)));
    }

    [Theory]
    [InlineData("bom")]
    [InlineData("cr")]
    [InlineData("lf")]
    [InlineData("utf8")]
    [InlineData("empty")]
    public void NoncanonicalEncodingIsRejected(string mode)
    {
        using var f = new Fixture();
        var bytes = Encoding.UTF8.GetBytes(f.Request);
        f.RequestBytes = mode switch
        {
            "bom" => [0xef, 0xbb, 0xbf, .. bytes],
            "cr" => Encoding.UTF8.GetBytes(f.Request.Replace("\n", "\r\n", StringComparison.Ordinal)),
            "lf" => bytes[..^1],
            "utf8" => [0xff, 10],
            _ => [],
        };
        f.Reject("REQUEST_ENCODING_INVALID");
    }

    [Theory]
    [InlineData("../escape.lean")]
    [InlineData("/tmp/probe.lean")]
    [InlineData("missing.lean")]
    [InlineData(".")]
    public void InvalidProbePathIsRejected(string path)
    {
        using var f = new Fixture();
        f.Reject("PROBE_PATH_INVALID", f.Request.Replace("probe.lean", path, StringComparison.Ordinal));
    }

    [Fact]
    public void ProbeSymlinkEscapeIsRejected()
    {
        using var f = new Fixture();
        using var outside = new TemporaryDirectory();
        Directory.CreateSymbolicLink(Path.Combine(f.Root, "alias"), outside.Path);
        TemporaryFileSystem.File.WriteAllText(Path.Combine(outside.Path, "probe.lean"), Source, Encoding.UTF8);
        f.Reject("PROBE_PATH_INVALID", f.Request.Replace("probe.lean", "alias/probe.lean", StringComparison.Ordinal));
    }

    [Theory]
    [InlineData("ATOM_ABSENT")]
    [InlineData("ATOM_AMBIGUOUS")]
    [InlineData("CHAIN_PARENT")]
    [InlineData("CONTEXT_MISMATCH")]
    [InlineData("NOT_RESIDUAL_OPEN")]
    [InlineData("COVERAGE_PRESENT")]
    [InlineData("QUARANTINE_PRESENT")]
    [InlineData("DISPOSITION_PRESENT")]
    [InlineData("NONPROPOSITIONAL_PRESENT")]
    [InlineData("UNRESOLVED_SUBITEMS_PRESENT")]
    [InlineData("OCCURRENCE_INDEX_REQUIRED")]
    [InlineData("OCCURRENCE_MISSING")]
    [InlineData("SOURCE_MISSING")]
    [InlineData("ATOMIZER_NONE")]
    public void GuardsRunBeforeProbeChecks(string code)
    {
        using var f = new Fixture();
        var entry = f.Target;
        entry = code switch
        {
            "CHAIN_PARENT" => entry with { Receipts = entry.Receipts with { ChainAtoms = [new string('f', 64)] } },
            "NOT_RESIDUAL_OPEN" => entry with { ProjectedStatus = new(DigestionMigrationState.Partial, DigestionTruthState.Open) },
            "COVERAGE_PRESENT" => entry with { Coverage = [new("D5/S0/Carrier/Probe", null)] },
            "QUARANTINE_PRESENT" => entry with { Receipts = entry.Receipts with { Quarantine = new("blocked", "supply witness", "missing-prerequisite") } },
            "DISPOSITION_PRESENT" => entry with { Receipts = entry.Receipts with { CoverDisposition = new(new(DigestionMigrationState.Partial, DigestionTruthState.Closed), ["D5/S0/Carrier/Probe"], []) } },
            "NONPROPOSITIONAL_PRESENT" => entry with { Receipts = entry.Receipts with { Nonpropositional = new("reason", null, null) } },
            "UNRESOLVED_SUBITEMS_PRESENT" => entry with { Receipts = entry.Receipts with { UnresolvedSubitems = ["live"] } },
            "ATOMIZER_NONE" => entry with { Atomizer = AtomizerRegistry.NoAtomizerId },
            _ => entry,
        };
        f.Context = f.Context.WithEntries(f.Context.Ledger.RequireDigestionEntries().Select(e => e.AtomId == f.Id ? entry : e));
        if (code == "ATOM_AMBIGUOUS")
        {
            var source = f.Context.Ledger.RequireDigestionSources().Single();
            f.Context = f.Context with { Ledger = f.Context.Ledger.WithDigestionSources([source, source with { SourceId = "second", Entries = [entry with { SourceId = "second" }] }]) };
        }
        if (code == "ATOMIZER_NONE") f.Context = f.Context with { Ledger = f.Context.Ledger.WithDigestionSources([
            f.Context.Ledger.RequireDigestionSources().Single() with { Atomizer = AtomizerRegistry.NoAtomizerId }]) };
        if (code == "OCCURRENCE_MISSING") f.Context = f.Context with { SourceBytes = Encoding.UTF8.GetBytes("Other text.\n") };
        if (code == "OCCURRENCE_INDEX_REQUIRED") f.Context = f.Context with { SourceBytes = [.. f.Context.SourceBytes, .. f.Context.SourceBytes] };
        f.ResetRaw(code != "SOURCE_MISSING");
        f.Probe("import D5.Forbidden\n");
        var request = f.Request;
        if (code == "ATOM_ABSENT") request = request.Replace(f.Id, new string('f', 64), StringComparison.Ordinal);
        if (code == "CONTEXT_MISMATCH") request = request.Replace("previous_atom_id = 'source-boundary'", "previous_atom_id = '" + new string('f', 64) + "'", StringComparison.Ordinal);
        f.Reject(code, request);
    }

    [Fact]
    public void ContextPrecedesVerbSpecificStateAndChainPrecedesContext()
    {
        using var f = new Fixture();
        var request = f.Request.Replace("previous_atom_id = 'source-boundary'", "previous_atom_id = '" + new string('f', 64) + "'", StringComparison.Ordinal);
        var target = f.Target with { ProjectedStatus = new(DigestionMigrationState.Partial, DigestionTruthState.Open) };
        f.Context = f.Context.WithEntries([target]);
        f.ResetRaw();
        f.Reject("CONTEXT_MISMATCH", request);
        f.Context = f.Context.WithEntries([target with { Receipts = target.Receipts with { ChainAtoms = [new string('f', 64)] } }]);
        f.ResetRaw();
        f.Reject("CHAIN_PARENT", request);
    }

    [Fact]
    public void WritesHashOfVerbatimProbeSortsDeclarationsReplaysAndClears()
    {
        using var f = new Fixture();
        var before = f.LedgerImage();
        var source = Source.Replace("by trivial", "by\n  trivial", StringComparison.Ordinal) + "-- preserved bytes α\n";
        // A comment after the prints is still a trailing print block in the source dialect.
        f.Probe(source);
        var result = f.Run();
        Assert.True(result.Success, result.Error);
        var entry = Assert.Single(BackfillInventoryLoader.LoadRoot(f.Root).RequireDigestionEntries());
        var receipt = Assert.IsType<DigestionUpstream>(entry.Receipts.Upstream);
        Assert.Equal(new[] { "Nat.add_comm", "True.intro" }, receipt.Declarations.ToArray());
        Assert.Equal("sha256:" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(source))), receipt.ProbeSha256);
        Assert.Equal(Encoding.UTF8.GetBytes(source), File.ReadAllBytes(Path.Combine(f.Root, f.ProbePath)));
        Assert.Equal($"SETTLE_UPSTREAM atom_id={f.Id} state=upstream-closed probe={f.ProbePath} declarations=2 axioms=[Classical.choice,Quot.sound,propext] mathlib_rev={new string('a', 40)}\n", result.Output);
        var settled = f.LedgerImage();
        var applies = f.ApplyCalls;
        Assert.True(f.Run().Success);
        Assert.Equal(settled, f.LedgerImage());
        Assert.Equal(applies, f.ApplyCalls);
        f.Reject("UPSTREAM_CONFLICT", f.Request.Replace("reason", "different reason", StringComparison.Ordinal));
        var cleared = f.Run(clear: true);
        Assert.True(cleared.Success, cleared.Error);
        Assert.False(File.Exists(Path.Combine(f.Root, f.ProbePath)));
        Assert.Equal(before, f.LedgerImage());
        f.Reject("UPSTREAM_ABSENT", clear: true);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void RoundTripFailureNeverWrites(bool unstable)
    {
        using var f = new Fixture();
        var calls = 0;
        f.Writer = entry => unstable ? [.. BackfillInventoryWriter.WriteAtom(entry), .. Encoding.UTF8.GetBytes(new string('\n', ++calls))]
            : [.. Encoding.UTF8.GetBytes("receipts: []\n")];
        f.Reject("ROUND_TRIP_FAILED");
    }

    [Theory]
    [InlineData(false, 1)]
    [InlineData(false, 2)]
    [InlineData(true, 1)]
    public void TransactionFailureRestoresProbeAndLedger(bool clear, int failAt)
    {
        using var f = new Fixture();
        if (clear) Assert.True(f.Run().Success);
        var before = f.LedgerImage();
        var commits = 0;
        f.Apply = (root, current, updates) => IngestCommand.ApplyLedgerUpdatesAtomically(root, current, updates, (pending, target) =>
        {
            if (++commits == failAt) throw new IOException("injected failure");
            File.Move(pending, target, true);
        });
        var result = f.Run(clear: clear);
        Assert.False(result.Success);
        Assert.StartsWith("SETTLE_UPSTREAM_INVALID INFRASTRUCTURE", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, f.LedgerImage());
    }

    [Theory]
    [InlineData("PROBE_FAILED")]
    [InlineData("PROBE_AXIOMS")]
    [InlineData("DECLARATION_UNRESOLVED")]
    [InlineData("INFRASTRUCTURE")]
    public void ProbeErrorsUseCommandFailureContract(string code)
    {
        using var f = new Fixture();
        if (code == "INFRASTRUCTURE") f.Runner.Failure = new TimeoutException("hang guard");
        else if (code == "PROBE_FAILED") f.Runner.Results.Enqueue(new(1, [], []));
        else if (code == "PROBE_AXIOMS") f.Runner.Results.Enqueue(new(0, Encoding.UTF8.GetBytes("'probe' depends on axioms: [secret]\n"), []));
        else
        {
            f.Runner.Results.Enqueue(new(0, Encoding.UTF8.GetBytes(Output), []));
            f.Runner.Results.Enqueue(new(1, Encoding.UTF8.GetBytes("Unknown constant `Nat.add_comm`"), []));
        }
        f.Reject(code);
    }

    [Fact]
    public void InvalidArgumentsAndTomlAreRejected()
    {
        using var f = new Fixture();
        foreach (var args in new string[][] { [], ["--clear", f.Id], ["--request", "r", "--base", "b", "--reverify"],
                     ["--request", "r", "--clear", f.Id, "--base", "b"], ["--clear", "bad", "--base", "b"] })
            Assert.StartsWith("SETTLE_UPSTREAM_INVALID ARGUMENTS_INVALID", f.Run(arguments: args).Error, StringComparison.Ordinal);
        f.Reject("REQUEST_KEYS_INVALID", "atom_id = [\n");
    }

    internal sealed class Fixture : IDisposable
    {
        private readonly ProbeFixture probe = new();
        internal string Root => probe.Root;
        internal CannedRunner Runner => probe.Runner;
        internal AtomContextFixture Context { get; set; } = AtomContextFixture.Create("## Claim\n\nProse.\n");
        internal DigestionLedgerEntry Target => Context.Ledger.RequireDigestionEntries().First();
        internal string Id { get; }
        internal string ProbePath => "Meta/Digestion/upstream/" + Id + ".lean";
        internal string Request { get; }
        internal byte[]? RequestBytes { get; set; }
        internal int ApplyCalls { get; private set; }
        internal Func<DigestionLedgerEntry, ImmutableArray<byte>> Writer { get; set; } = BackfillInventoryWriter.WriteAtom;
        internal Action<string, RawRepositorySnapshot, ImmutableArray<IngestCommand.LedgerUpdate>> Apply { get; set; } =
            (root, current, updates) => IngestCommand.ApplyLedgerUpdatesAtomically(root, current, updates);
        internal Fixture()
        {
            Id = Target.AtomId;
            Request = $"atom_id = '{Id}'\njustification = 'reason'\ndeclarations = ['True.intro', 'Nat.add_comm']\nprobe = 'probe.lean'\nprevious_atom_id = 'source-boundary'\nnext_atom_id = 'source-boundary'\n";
            ResetRaw();
            Probe(Source);
        }
        internal void ResetRaw(bool includeSource = true)
        {
            var ledger = Path.Combine(Root, BackfillInventoryLoader.RootPath);
            if (Directory.Exists(ledger)) Directory.Delete(ledger, true);
            if (!includeSource) File.Delete(Path.Combine(Root, AtomContextFixture.SourcePath));
            var raw = RawRepositorySnapshot.Create(Context.RawSnapshot(includeSource).Entries.Append(RawRepositoryEntry.FromText("lake-manifest.json", Manifest)));
            WriteFiles(Root, raw);
        }
        internal void Probe(string source) => TemporaryFileSystem.File.WriteAllBytes(Path.Combine(Root, "probe.lean"), Encoding.UTF8.GetBytes(source));
        internal RawRepositorySnapshot Raw() => RawRepositorySnapshot.Create(Directory.EnumerateFiles(Root, "*", SearchOption.AllDirectories)
            .Where(path => !Path.GetRelativePath(Root, path).StartsWith(".lake/", StringComparison.Ordinal) && !Path.GetRelativePath(Root, path).StartsWith("alias/", StringComparison.Ordinal))
            .Select(path => new RawRepositoryEntry(Path.GetRelativePath(Root, path), [.. File.ReadAllBytes(path)])));
        internal string LedgerImage() => string.Join('\n', Raw().Entries.Where(e => e.Path.StartsWith("Meta/Digestion/", StringComparison.Ordinal))
            .OrderBy(e => e.Path, StringComparer.Ordinal).Select(e => e.Path + ":" + Convert.ToHexString(e.Bytes.AsSpan())));
        internal CommandResult Run(string? request = null, bool clear = false, IReadOnlyList<string>? arguments = null)
        {
            var raw = Raw();
            return SettleUpstreamCommand.Run(Root, new FakeRepositoryGateway(RawChangeSet.Create([]), raw, raw),
                arguments ?? (clear ? ["--clear", Id, "--base", "baseline"] : ["--request", "request.toml", "--base", "baseline"]),
                Writer, (_, _) => [.. RequestBytes ?? Encoding.UTF8.GetBytes(request ?? Request)],
                (root, current, updates) => { ApplyCalls++; Apply(root, current, updates); },
                () => new UpstreamProbeVerifier(Runner, "synthetic-lake", PinnedProductionBudgets.UpstreamProbeBudget));
        }
        internal void Reject(string code, string? request = null, bool clear = false)
        {
            var before = LedgerImage();
            var calls = ApplyCalls;
            var result = Run(request, clear);
            Assert.False(result.Success, result.Output);
            Assert.StartsWith("SETTLE_UPSTREAM_INVALID " + code + " ", result.Error, StringComparison.Ordinal);
            Assert.Equal(before, LedgerImage());
            Assert.Equal(calls, ApplyCalls);
        }
        public void Dispose() => probe.Dispose();
    }
}
