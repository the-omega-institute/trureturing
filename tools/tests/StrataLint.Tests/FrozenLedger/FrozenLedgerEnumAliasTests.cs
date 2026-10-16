using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AuthenticatedEnumAliasRemovesOnlyTheDuplicateOldRoot(bool privateOwner)
    {
        var fixture = AliasFixture(privateOwner: privateOwner);
        Assert.True(AliasEquivalent(fixture));
        Assert.False(AliasEquivalent(fixture, supplyWitness: false));
    }

    [Fact]
    public void AuthenticatedEnumAliasRequiresTheActualOldBody()
    {
        var fixture = AliasFixture(aliasMaterial: "statement-v1(uparams=[],type=other,value=constant-zero)");
        Assert.True(fixture.Witness.TryAuthenticate(RepoPathFor("A"), fixture.State.Records[RepoPathFor("A")], out _));
        Assert.False(AliasEquivalent(fixture));
    }

    [Theory]
    [InlineData("unrelated-id")]
    [InlineData("missing-unrelated")]
    [InlineData("alias-id")]
    public void AuthenticatedEnumAliasRequiresTheCompleteProtectedModule(string fault)
    {
        var fixture = AliasFixture();
        var rows = fixture.OldReport.Files[RepoPathFor("A")].Declarations;
        rows = fault == "missing-unrelated" ? rows.RemoveAt(0)
            : rows.Select((row, index) => index == (fault == "alias-id" ? rows.Length - 1 : 0)
                ? row with { PrecomputedStatementId = "sha256:" + new string('f', 64) } : row).ToImmutableArray();
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
            { [PathFor("A")] = new([], rows) });
        var witness = RawLeanReportArtifact.ReadFrozenWitness(RawLeanReportArtifact.Write(fixture.Before, report).AsSpan());
        Assert.False(AliasEquivalent(fixture with { Witness = witness }));
    }

    [Theory]
    [InlineData("ctor-missing")]
    [InlineData("ctor-excluded")]
    [InlineData("ctor-kind")]
    [InlineData("alias-excluded")]
    [InlineData("ordinary-missing")]
    [InlineData("ordinary-added")]
    [InlineData("owner-kind")]
    public void AuthenticatedEnumAliasPreservesEveryOtherRoot(string fault)
    {
        var fixture = AliasFixture(candidateFault: fault);
        Assert.False(AliasEquivalent(fixture));
    }

    [Theory]
    [InlineData("  | left | right", "  | right | left")]
    [InlineData("def value : Nat := 1", "def value : Nat := 2")]
    [InlineData("by trivial", "by exact True.intro")]
    [InlineData("set_option autoImplicit false", "set_option autoImplicit true")]
    public void AuthenticatedEnumAliasRetainsCompleteRawSource(string before, string after)
    {
        var fixture = AliasFixture(candidateSource: AliasSource.Replace(before, after, StringComparison.Ordinal));
        Assert.False(AliasEquivalent(fixture));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AuthenticatedEnumAliasRetainsTransitiveImports(bool missing)
    {
        var fixture = AliasFixture(importedSource: "def data : Nat := 1\n",
            candidateImportedSource: missing ? null : "def data : Nat := 2\n");
        Assert.False(AliasEquivalent(fixture));
    }

    [Fact]
    public void AuthenticatedEnumAliasDoesNotAcceptQuotedDotOwnerCollision()
    {
        var fixture = AliasFixture(aliasKey: "ns(ns(n0,10:Owner.Flag),9:toCtorIdx)");
        Assert.False(AliasEquivalent(fixture));
    }

    [Fact]
    public void AuthenticatedEnumAliasIgnoresUncommittedDisplayMetadata()
    {
        var fixture = AliasFixture(displayName: "untrusted display name");
        Assert.True(AliasEquivalent(fixture));
    }

    [Fact]
    public void AuthenticatedEnumAliasDoesNotLoadHistoricalMaterials()
    {
        var fixture = AliasFixture();
        Assert.True(AliasEquivalent(fixture));
        Assert.True(fixture.Witness.TryAuthenticate(RepoPathFor("A"), fixture.State.Records[RepoPathFor("A")], out _));
    }

    private const string AliasSource = "set_option autoImplicit false\nnamespace Owner\ninductive Flag\n  | left | right\nend Owner\ndef value : Nat := 1\ntheorem a : True := by trivial\n";

    private sealed record EnumAliasFixture(RepositorySnapshot Before, RepositorySnapshot After,
        FrozenStateCatalog State, LeanAxiomReport OldReport, LeanAxiomReport CurrentReport, FrozenStatementWitness Witness);

    private static EnumAliasFixture AliasFixture(bool privateOwner = false, string? aliasMaterial = null,
        string? aliasKey = null, string? displayName = null, string? candidateFault = null,
        string? candidateSource = null, string? importedSource = null, string? candidateImportedSource = null,
        string privateModule = "D5.S0.Carrier.A", int privateIndex = 0, bool numericPrivateIndex = true,
        bool unicodeOwner = false, bool wrongOtherRootKind = false, string? ownerKey = null)
    {
        var owner = privateOwner ? "_private." + privateModule : "";
        string Key(string name)
        {
            if (unicodeOwner) name = name.Replace("Flag", "旗帜", StringComparison.Ordinal);
            var key = "n0";
            if (ownerKey is not null && (name == "Owner.Flag" || name.StartsWith("Owner.Flag.", StringComparison.Ordinal)))
            {
                key = ownerKey;
                foreach (var part in name["Owner.Flag".Length..].Split('.', StringSplitOptions.RemoveEmptyEntries))
                    key = $"ns({key},{Encoding.UTF8.GetByteCount(part)}:{part})";
                return key;
            }
            var usePrivate = privateOwner && name.StartsWith(unicodeOwner ? "Owner.旗帜" : "Owner.Flag", StringComparison.Ordinal);
            foreach (var part in (usePrivate ? owner : "").Split('.', StringSplitOptions.RemoveEmptyEntries))
                key = $"ns({key},{Encoding.UTF8.GetByteCount(part)}:{part})";
            if (usePrivate) key = numericPrivateIndex ? $"nn({key},{privateIndex})" : $"ns({key},1:{privateIndex})";
            foreach (var part in name.Split('.')) key = $"ns({key},{Encoding.UTF8.GetByteCount(part)}:{part})";
            return key;
        }
        LeanDeclaration Row(string name, string kind, string? material = null) =>
            new(name, kind, material ?? "old material " + name, []) { NameKey = Key(name) };
        var alias = Row("Owner.Flag.toCtorIdx", "def", aliasMaterial
            ?? $"statement-v1(uparams=[],type=ep(bd,ec({Key("Owner.Flag")},[]),ec(ns(n0,3:Nat),[])),value=ec({Key("Owner.Flag.ctorIdx")},[]))")
            with { NameKey = aliasKey ?? Key("Owner.Flag.toCtorIdx"), Name = displayName ?? "Owner.Flag.toCtorIdx" };
        var oldRows = new[] { Row("Owner.Flag", "inductive"), Row("Owner.Flag.left", "constructor"),
            Row("Owner.Flag.right", "constructor"), Row("Owner.Flag.ctorIdx", "def"),
            Row("Owner.Flag.noConfusion", "def"), Row("a", "theorem"), Row("value", wrongOtherRootKind ? "theorem" : "def"), alias }
            .OrderBy(static row => row.NameKey, StringComparer.Ordinal).ToImmutableArray();
        var currentRows = oldRows.Where(row => row.NameKey != alias.NameKey).Select(row =>
            row.NameKey == Key("Owner.Flag.noConfusion") ? row with { TypeRepresentation = "new compiled noConfusion" } : row).ToImmutableArray();
        if (candidateFault is "ctor-missing" or "ordinary-missing")
            currentRows = currentRows.Where(row => row.NameKey != Key(candidateFault == "ctor-missing" ? "Owner.Flag.ctorIdx" : "value")).ToImmutableArray();
        if (candidateFault is "ctor-excluded" or "ctor-kind" or "owner-kind")
            currentRows = currentRows.Select(row => row.NameKey == Key(candidateFault == "owner-kind" ? "Owner.Flag" : "Owner.Flag.ctorIdx")
                ? candidateFault == "ctor-excluded" ? row with { IncludeInStatement = false } : row with { Kind = "theorem" } : row).ToImmutableArray();
        if (candidateFault == "alias-excluded") currentRows = currentRows.Add(alias with { IncludeInStatement = false });
        if (candidateFault == "ordinary-added") currentRows = currentRows.Add(Row("extra", "def"));
        var oldReport = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport> { [PathFor("A")] = new([], oldRows) });
        var currentReport = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport> { [PathFor("A")] = new([], currentRows) });
        var source = privateOwner ? AliasSource.Replace("inductive Flag", "private inductive Flag", StringComparison.Ordinal) : AliasSource;
        if (unicodeOwner) source = source.Replace("Flag", "旗帜", StringComparison.Ordinal);
        RepositorySnapshot MakeSnapshot(string text, string pin, string? imported)
        {
            if (importedSource is not null) text = "import D5.S0.Carrier.B\n" + text;
            var record = FrozenStateRecord.FromReport(RepoPathFor("A"), oldReport.Files[RepoPathFor("A")]);
            var files = new List<RepositoryFile> { TextFile(PathFor("A"), text),
                TextFile("Golden/Frozen/state/" + PathFor("A") + ".json", Encoding.UTF8.GetString(FrozenStateRecord.Encode(record.StatementId, record.Declarations).AsSpan())),
                TextFile("lean-toolchain", "leanprover/lean4:" + pin + "\n"), TextFile("lake-manifest.json", MathlibManifest(new string(pin == "v4.33.0" ? 'a' : 'b', 40))) };
            if (imported is not null) files.Add(TextFile(PathFor("B"), imported));
            return Snapshot(files);
        }
        var before = MakeSnapshot(source, "v4.33.0", importedSource);
        var after = MakeSnapshot(candidateSource ?? source, "v4.35.0", candidateImportedSource);
        // The historical witness carries only commitments and has no material archive.
        var witnessSnapshot = Snapshot(before.Files.Values.Where(static file => file.Path.Value != PathFor("B")));
        var witness = RawLeanReportArtifact.ReadFrozenWitness(RawLeanReportArtifact.Write(witnessSnapshot, oldReport).AsSpan());
        return new(before, after, FrozenStateCatalog.Load(before), oldReport, currentReport, witness);
    }

    private static bool AliasEquivalent(EnumAliasFixture fixture, bool supplyWitness = true) =>
        LeanPropositionSourceComparer.AreEquivalent(fixture.Before, fixture.After,
            ImmutableHashSet.Create(RepoPathFor("A")), fixture.State, fixture.CurrentReport,
            supplyWitness ? fixture.Witness : null);
}
