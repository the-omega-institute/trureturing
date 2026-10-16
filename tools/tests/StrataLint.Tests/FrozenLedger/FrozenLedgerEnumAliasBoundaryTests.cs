using System.Collections.Immutable;
using System.Text;
using System.Text.Json.Nodes;
using StrataLint.Cli;
using StrataLint.Engine;
using Trureturing.Truth;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Theory]
    [InlineData("D5.S0.Carrier.B", 0, true)]
    [InlineData("D5.S0.Carrier.A", 1, true)]
    [InlineData("D5.S0.Carrier.A", 0, false)]
    public void AuthenticatedEnumAliasRequiresExactTypedPrivateOrigin(string module, int index, bool numeric)
    {
        var fixture = AliasFixture(privateOwner: true, privateModule: module,
            privateIndex: index, numericPrivateIndex: numeric);
        Assert.False(AliasEquivalent(fixture));
    }

    [Theory]
    [InlineData("ns(nn(ns(n0,5:Owner),7),4:Flag)")]
    [InlineData("nn(ns(ns(n0,5:Owner),4:Flag),7)")]
    public void AuthenticatedEnumAliasRejectsNumericPublicOwnerComponents(string ownerKey)
    {
        var fixture = AliasFixture(ownerKey: ownerKey);
        Assert.True(fixture.Witness.TryAuthenticate(RepoPathFor("A"), fixture.State.Records[RepoPathFor("A")], out _));
        Assert.False(AliasEquivalent(fixture));
        Assert.False(new MathlibUpgradeFrozenLedgerReplacementAuthorization(fixture.Before, fixture.After, fixture.Witness)
            .IsAuthorized(ImmutableHashSet.Create(RepoPathFor("A")), fixture.State, fixture.CurrentReport));
    }

    [Theory]
    [InlineData(false, true, true)]
    [InlineData(false, false, true)]
    [InlineData(false, true, false)]
    [InlineData(true, false, false)]
    [InlineData(true, true, false)]
    [InlineData(true, false, true)]
    public void AuthenticatedEnumAliasRequiresMatchingSourceVisibility(bool privateKey, bool privateBefore, bool privateAfter)
    {
        var fixture = AliasFixture(privateOwner: privateKey);
        RepositorySnapshot WithVisibility(RepositorySnapshot snapshot, bool isPrivate) => Snapshot(snapshot.Files.Values
            .Select(file => file.Path == RepoPathFor("A")
                ? TextFile(PathFor("A"), isPrivate
                    ? AliasSource.Replace("inductive Flag", "private inductive Flag", StringComparison.Ordinal)
                    : AliasSource)
                : file));
        fixture = fixture with { Before = WithVisibility(fixture.Before, privateBefore), After = WithVisibility(fixture.After, privateAfter) };
        Assert.True(fixture.Witness.TryAuthenticate(RepoPathFor("A"), fixture.State.Records[RepoPathFor("A")], out _));
        Assert.False(AliasEquivalent(fixture));
        Assert.False(new MathlibUpgradeFrozenLedgerReplacementAuthorization(fixture.Before, fixture.After, fixture.Witness)
            .IsAuthorized(ImmutableHashSet.Create(RepoPathFor("A")), fixture.State, fixture.CurrentReport));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AuthenticatedEnumAliasSupportsUtf8OwnerKeys(bool privateOwner)
    {
        Assert.True(AliasEquivalent(AliasFixture(privateOwner: privateOwner, unicodeOwner: true)));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AuthenticatedEnumAliasStillChecksExplicitRootKinds(bool privateOwner)
    {
        Assert.False(AliasEquivalent(AliasFixture(privateOwner: privateOwner, wrongOtherRootKind: true)));
    }

    [Fact]
    public void AuthenticatedEnumAliasRetainsProofGeneratorSource()
    {
        const string generator = "by\n  run_tac Lean.addDecl placeholder\n  trivial";
        var fixture = AliasFixture(candidateSource: AliasSource.Replace("by trivial", generator, StringComparison.Ordinal));
        Assert.False(AliasEquivalent(fixture));
    }

    [Fact]
    public void AuthenticatedEnumAliasWitnessCannotWeakenNormalReportSourceBinding()
    {
        var fixture = AliasFixture();
        var node = JsonNode.Parse(Encoding.UTF8.GetString(RawLeanReportArtifact.Write(fixture.Before, fixture.OldReport).AsSpan()))!;
        node["modules"]![0]!["source_sha256"] = "sha256:" + new string('f', 64);
        var bytes = StructuredCanonicalWriter.WriteJson(node.ToJsonString());
        var witness = RawLeanReportArtifact.ReadFrozenWitness(bytes.AsSpan());
        Assert.True(AliasEquivalent(fixture with { Witness = witness }));
        Assert.Throws<FormatException>(() => RawLeanReportArtifact.Read(bytes.AsSpan(), fixture.Before));
    }

    [Fact]
    public void AuthenticatedEnumAliasWitnessRejectsDuplicateDeclarationKeys()
    {
        var fixture = AliasFixture();
        var rows = fixture.OldReport.Files[RepoPathFor("A")].Declarations;
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
            { [PathFor("A")] = new([], rows.Add(rows[0] with { Kind = "theorem" })) });
        var bytes = RawLeanReportArtifact.Write(fixture.Before, report);
        Assert.Throws<FormatException>(() => RawLeanReportArtifact.ReadFrozenWitness(bytes.AsSpan()));
    }

    [Fact]
    public void AuthenticatedEnumAliasDoesNotReplaceEffectivePinBump()
    {
        var fixture = AliasFixture();
        var paths = ImmutableHashSet.Create(RepoPathFor("A"));
        Assert.True(new MathlibUpgradeFrozenLedgerReplacementAuthorization(fixture.Before, fixture.After, fixture.Witness)
            .IsAuthorized(paths, fixture.State, fixture.CurrentReport));
        var after = Snapshot(fixture.After.Files.Values.Where(static file =>
                file.Path.Value is not ("lean-toolchain" or "lake-manifest.json"))
            .Concat(fixture.Before.Files.Values.Where(static file =>
                file.Path.Value is "lean-toolchain" or "lake-manifest.json")));
        Assert.False(new MathlibUpgradeFrozenLedgerReplacementAuthorization(fixture.Before, after, fixture.Witness)
            .IsAuthorized(paths, fixture.State, fixture.CurrentReport));
    }

    [Fact]
    public void AuthenticatedEnumAliasStillChecksNonDriftRetainedAxioms()
    {
        var fixture = AliasFixture();
        var row = new LeanDeclaration("b", "theorem", "True", []) { NameKey = "ns(n0,1:b)" };
        var report = new LeanFileReport([], [row]);
        var state = FrozenStateRecord.FromReport(RepoPathFor("B"), report);
        RepositorySnapshot WithB(RepositorySnapshot snapshot) => Snapshot(snapshot.Files.Values
            .Append(TextFile(PathFor("B"), "theorem b : True := by trivial\n"))
            .Append(TextFile("Golden/Frozen/state/" + PathFor("B") + ".json",
                Encoding.UTF8.GetString(FrozenStateRecord.Encode(state.StatementId, state.Declarations).AsSpan()))));
        var before = WithB(fixture.Before);
        var after = WithB(fixture.After);
        var candidate = LeanAxiomReport.Create(fixture.CurrentReport.Files.ToDictionary(static pair => pair.Key.Value,
            static pair => pair.Value));
        var reports = candidate.Files.ToDictionary(static pair => pair.Key.Value, static pair => pair.Value);
        reports.Add(PathFor("B"), report with { Declarations = [row with { Axioms = ["Nonstandard.axiom"] }] });
        Assert.False(new MathlibUpgradeFrozenLedgerReplacementAuthorization(before, after, fixture.Witness)
            .IsAuthorized(ImmutableHashSet.Create(RepoPathFor("A")), FrozenStateCatalog.Load(before), LeanAxiomReport.Create(reports)));
    }

    [Fact]
    public void AuthenticatedEnumAliasDiagnosticsAndAuthorizationShareTheComparison()
    {
        var fixture = AliasFixture();
        var paths = ImmutableHashSet.Create(RepoPathFor("A"));
        Assert.Empty(MathlibUpgradePropositionSourceDiagnostics.FindFailures(fixture.Before, fixture.After,
            paths, fixture.State, fixture.CurrentReport, fixture.Witness));
        Assert.Equal(RepoPathFor("A").Value, Assert.Single(MathlibUpgradePropositionSourceDiagnostics.FindFailures(
            fixture.Before, fixture.After, paths, fixture.State, fixture.CurrentReport)).Value);
    }
}
