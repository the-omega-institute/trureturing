using System.Collections.Immutable;
using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class LedgerAlignWriterTests
{
    private const string PortSource = """
        import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
        namespace WeierstrassCurve.Affine.Point
        variable {F : Type*} [Field F] {W : Affine F} [DecidableEq F]
        lemma a (P Q : W.Point) :
            ∃ t : F, t ≠ 0 ∧ t • sym2x (P + Q) (P - Q) =
              (addSubMap W · |>.eval <| sym2x P Q) := by
          exact sym2x_add_sub_eq_addSubMap_sym2x P Q
        end WeierstrassCurve.Affine.Point
        """;

    [Fact]
    public void AdoptedUpstreamPortRetiresThroughCanonicalPublicationAndStaysRetired()
    {
        var port = ModuleWithReport("A", PortSource, "∀ P Q, ∃ t, t ≠ 0 ∧ t • sym2x (P + Q) (P - Q) = addSubMap W (sym2x P Q)");
        var original = BuildCatalog(port, Module("B") with { Imports = ["A"] });
        using var fixture = PortFixture(original, port, Module("B"));
        InstallPort(fixture, original);
        var retainedPin = fixture.StatePin("B");

        var result = fixture.Align("--base", "protected", "--retire-upstream-port", PathFor("A"));

        Assert.True(result.Success, result.Error);
        Assert.Contains("LEDGER_RETIRE upstream_ports=1", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("registrations=1", result.Output, StringComparison.Ordinal);
        Assert.False(fixture.StateExists("A"));
        Assert.Equal(retainedPin, fixture.StatePin("B"));
        Assert.Empty(Assert.Single(ReadRepairEvents(fixture.AcceptedFiles())).Payload.GetProperty("prerequisite_frozen_node_ids").EnumerateArray());
        Assert.Single(fixture.AcceptedFiles());
        Assert.All(ReadRepairEvents(fixture.AcceptedFiles()), item => Assert.Equal("Freeze", item.EventType));
        var after = fixture.AllPublishedBytes();
        Assert.True(fixture.FromAccepted().Success);
        Assert.True(fixture.Align().Success);
        Assert.Equal(after, fixture.AllPublishedBytes());
        Assert.False(fixture.Align("--base", "protected", "--retire-upstream-port", PathFor("A")).Success);
        Assert.Equal(after, fixture.AllPublishedBytes());
    }

    [Theory]
    [InlineData("no-base")]
    [InlineData("same-pin")]
    [InlineData("unowned-base")]
    [InlineData("existing-source")]
    [InlineData("remaining-import")]
    [InlineData("state-conflict")]
    [InlineData("conflicting-selector")]
    [InlineData("from-accepted")]
    public void UpstreamPortRefusalLeavesEveryPublishedByteIntact(string variant)
    {
        var port = ModuleWithReport("A", PortSource, "∀ P Q, ∃ t, t ≠ 0 ∧ t • sym2x (P + Q) (P - Q) = addSubMap W (sym2x P Q)");
        var original = BuildCatalog(port, Module("B"));
        var consumer = Module("B") with { Imports = variant == "remaining-import" ? ["A"] : [] };
        var modules = variant == "existing-source" ? new[] { port, consumer } : [consumer];
        using var fixture = PortFixture(original, port, modules,
            samePin: variant == "same-pin", owned: variant != "unowned-base");
        InstallPort(fixture, original);
        if (variant == "state-conflict") fixture.InstallState("A", StatementId.Create("sha256:" + new string('f', 64)));
        var before = fixture.AllPublishedBytes();
        var options = new List<string> { "--retire-upstream-port", PathFor("A") };
        if (variant != "no-base") options.AddRange(["--base", "protected"]);
        if (variant == "conflicting-selector") options.AddRange(["--retire-registration", PathFor("A")]);
        if (variant == "from-accepted") options.Add("--from-accepted");

        var result = fixture.Align(options.ToArray());

        Assert.False(result.Success);
        Assert.Contains(variant switch
        {
            "no-base" or "from-accepted" => "USAGE",
            "same-pin" => "changed adopted mathlib pin",
            "unowned-base" => "protected-base frozen owner",
            "existing-source" => "cannot retire existing module",
            "remaining-import" => "still imports retired registration",
            "state-conflict" => "state/event statement_id conflict",
            "conflicting-selector" => "duplicate or conflicting module selector",
            _ => throw new InvalidOperationException(),
        }, result.Error, StringComparison.Ordinal);
        Assert.Equal(before, fixture.AllPublishedBytes());
    }

    private static AlignFixture PortFixture(FrozenMaterialCatalog original, ModuleSpec port,
        ModuleSpec consumer) => PortFixture(original, port, [consumer]);

    private static AlignFixture PortFixture(FrozenMaterialCatalog original, ModuleSpec port,
        ModuleSpec[] current, bool samePin = false, bool owned = true)
    {
        var entries = new List<RawRepositoryEntry>
        {
            RawRepositoryEntry.FromText("lean-toolchain", "leanprover/lean4:v4.24.0\n"),
            RawRepositoryEntry.FromText("lake-manifest.json", "{\"packages\":[{\"name\":\"mathlib\",\"type\":\"git\",\"rev\":\"" + new string(samePin ? 'b' : 'a', 40) + "\"}]}\n"),
        };
        if (owned)
        {
            entries.Add(RawRepositoryEntry.FromText(PathFor("A"), port.Source));
            entries.AddRange(EventFiles(original).Select(file => new RawRepositoryEntry(file.Path.Value, file.RawBytes)));
        }
        return new AlignFixture(current, [], RawRepositorySnapshot.Create(entries), adoptedPin: true);
    }

    private static void InstallPort(AlignFixture fixture, FrozenMaterialCatalog original)
    {
        fixture.InstallAccepted(original);
        foreach (var name in new[] { "A", "B" })
            fixture.InstallState(name, original.ByPath[RepoPathFor(name)].StatementId);
    }
}
