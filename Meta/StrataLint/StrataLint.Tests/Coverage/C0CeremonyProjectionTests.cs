using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class C0CeremonyProjectionTests
{
    private const string CheckCommandPath =
        "Meta/StrataLint/StrataLint.Cli/Admission/CheckCommand.cs";
    private const string NestedControllerPath =
        "Meta/StrataLint/StrataLint.Cli/Conservative/Nested/Worker.cs";
    private const string NestedCorpusSourcePath =
        "Meta/StrataLint/StrataLint.Cli/Golden/Nested/Schema.cs";
    private const string NestedCorpusDataPath =
        "Golden/cases/Nested/behavior.toml";

    [Fact]
    public void ProductionPolicyDiscoversNestedAnchorsWithoutReadingTower()
    {
        var snapshot = Snapshot();

        var anchors = C0CeremonyProjection.DiscoverAnchors(snapshot);

        Assert.Contains(anchors, item => item is
        {
            Kind: C0AnchorKind.Controller,
            Path: NestedControllerPath,
        });
        Assert.Contains(anchors, item => item is
        {
            Kind: C0AnchorKind.Corpus,
            Path: NestedCorpusSourcePath,
        });
        Assert.Contains(anchors, item => item is
        {
            Kind: C0AnchorKind.Corpus,
            Path: NestedCorpusDataPath,
        });
        Assert.DoesNotContain(
            anchors,
            static item => item.Path == RepositoryRules.TowerManifestPath);
        Assert.Contains(anchors, static item => item is
        {
            Kind: C0AnchorKind.Controller,
            Path: CheckCommandPath,
        });
        Assert.Contains(anchors, static item => item is
        {
            Kind: C0AnchorKind.Controller,
        } && item.Path.EndsWith(
            "/GitRepositoryGateway.FrozenLedger.cs",
            StringComparison.Ordinal));
        Assert.Contains(anchors, static item => item is
        {
            Kind: C0AnchorKind.Controller,
        } && item.Path.EndsWith(
            "/local-harness-gate.sh",
            StringComparison.Ordinal));
        Assert.Contains(anchors, static item => item is
        {
            Kind: C0AnchorKind.Controller,
        } && item.Path.EndsWith(
            "/lean-report-pair.sh",
            StringComparison.Ordinal));
        Assert.Contains(anchors, static item => item is
        {
            Kind: C0AnchorKind.Controller,
        } && item.Path.EndsWith(
            "/lean-inspector/inspect.sh",
            StringComparison.Ordinal));
        Assert.Contains(anchors, static item => item is
        {
            Kind: C0AnchorKind.Controller,
        } && item.Path.EndsWith(
            "/lean-inspector/Inspector.lean",
            StringComparison.Ordinal));
        var gate = Assert.Single(
            anchors,
            static item => item.Kind == C0AnchorKind.GateWiring);
        Assert.Equal(C0CeremonyProjection.GateWiringPath, gate.Path);
    }

    [Fact]
    public void ActualGateRejectsAProjectedCeremonyThatOmitsADiscoveredAnchor()
    {
        var snapshot = Snapshot();
        var certificate = snapshot.Files.Values.Single(static file =>
            file.Path.Value == C0CeremonyProjection.CertificatePath).RawBytes;
        var members = C0CeremonyProjection.CreateMembers(
            snapshot,
            certificate.AsSpan(),
            Identity());
        var omitted = members.Where(member =>
            !member.EndsWith(" " + NestedControllerPath, StringComparison.Ordinal)).ToImmutableArray();
        var syntax = Syntax(omitted);

        var rejected = Assert.IsType<TowerValidationOutcome.Rejected>(
            TowerManifestValidator.Validate(syntax, snapshot, RuleCatalog.CreateForTesting([], [])));

        Assert.Contains(rejected.Findings, static item => item is
        {
            Code: "TOWER-C0-ADDRESS",
            Component: C0CeremonyProjection.ComponentId,
        });
    }

    [Fact]
    public void CanonicalShapeRequiresExactlyOneGateWiringRecord()
    {
        var members = ImmutableArray.Create(
            "phase1-protected-content-admission",
            "phase2-dual-harness-conservative-extension",
            "c0/base-commit git-commit/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
            "c0/ceremony-commit convention/this-pr-merge-commit",
            "c0/controller git-sha1/bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb controller.cs",
            "c0/corpus git-sha1/cccccccccccccccccccccccccccccccccccccccc corpus.toml",
            "c0/gate-wiring git-sha1/dddddddddddddddddddddddddddddddddddddddd gate-a.sh",
            "c0/gate-wiring git-sha1/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee gate-b.sh",
            "c0/inaugural-certificate sha256/ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff certificate.json",
            "c0/preimage-commit git-commit/1111111111111111111111111111111111111111",
            "c0/preimage-tree git-tree/2222222222222222222222222222222222222222");

        Assert.False(C0CeremonyProjection.HasCanonicalShape(members));
    }

    [Fact]
    public void TowerProjectionPreservesNonC0BytesAndSecondPassIsByteExact()
    {
        var original = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("""
            schema_version: 1
            components:
              - id: before
                kind: artifact-classes
                members:
                  - F
                judged_by:
                  - bootstrap-pr-1
                verification: verified
              - id: conservative-extension-gate-c
                kind: phased-gate
                members:
                  - phase1-protected-content-admission
                  - phase2-dual-harness-conservative-extension
                  - "c0/base-commit git-commit/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                  - "c0/ceremony-commit convention/this-pr-merge-commit"
                  - "c0/controller git-sha1/bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb old.cs"
                  - "c0/corpus git-sha1/cccccccccccccccccccccccccccccccccccccccc old.toml"
                  - "c0/gate-wiring git-sha1/dddddddddddddddddddddddddddddddddddddddd gate.sh"
                  - "c0/inaugural-certificate sha256/eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee old.json"
                  - "c0/preimage-commit git-commit/ffffffffffffffffffffffffffffffffffffffff"
                  - "c0/preimage-tree git-tree/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                judged_by:
                  - bootstrap-pr-1
                verification: verified
            bootstrap:
              id: bootstrap-pr-1
              judge: open
              reason: "Godel boundary."
              genesis_event: sha256:fc2ee6be0dd3cabb9b6a9118592671c9d5a81f691b7b4ad07674d9c3037ce262
              commit: f3f471846dd81cfcc39ecaa386966fcf0b058464
              pull_request: 1
              verification: ASSUMED-UNVERIFIED
            """ + "\n"));
        var replacement = ImmutableArray.Create(
            "phase1-protected-content-admission",
            "phase2-dual-harness-conservative-extension",
            "c0/base-commit git-commit/1111111111111111111111111111111111111111",
            "c0/ceremony-commit convention/this-pr-merge-commit",
            "c0/controller git-sha1/2222222222222222222222222222222222222222 new.cs",
            "c0/corpus git-sha1/3333333333333333333333333333333333333333 new.toml",
            "c0/gate-wiring git-sha1/4444444444444444444444444444444444444444 gate.sh",
            "c0/inaugural-certificate sha256/5555555555555555555555555555555555555555555555555555555555555555 new.json",
            "c0/preimage-commit git-commit/6666666666666666666666666666666666666666",
            "c0/preimage-tree git-tree/7777777777777777777777777777777777777777");

        var first = C0TowerProjection.Write(original.AsSpan(), replacement);
        var second = C0TowerProjection.Write(first.AsSpan(), replacement);
        var text = Encoding.UTF8.GetString(first.AsSpan());

        var mismatch = Enumerable.Range(0, Math.Min(first.Length, second.Length))
            .FirstOrDefault(index => first[index] != second[index], -1);
        Assert.True(
            first.AsSpan().SequenceEqual(second.AsSpan()),
            $"projection drifted: first={first.Length} second={second.Length} mismatch={mismatch}\n"
            + Encoding.UTF8.GetString(first.AsSpan())
            + "\n--- second ---\n"
            + Encoding.UTF8.GetString(second.AsSpan()));
        Assert.StartsWith("schema_version: 1\ncomponents:\n  - id: before\n", text, StringComparison.Ordinal);
        Assert.Contains("c0/controller git-sha1/2222222222222222222222222222222222222222 new.cs", text, StringComparison.Ordinal);
        Assert.DoesNotContain("old.cs", text, StringComparison.Ordinal);
        Assert.EndsWith("verification: ASSUMED-UNVERIFIED\n", text, StringComparison.Ordinal);
    }

    private static C0CeremonyIdentity Identity() => new(
        new string('a', 40),
        new string('b', 40),
        new string('c', 40));

    private static TowerManifestSyntax Syntax(ImmutableArray<string> members) => new(
        1,
        [new TowerComponentSyntax(
            C0CeremonyProjection.ComponentId,
            "phased-gate",
            members,
            ["bootstrap-pr-1"],
            "verified")],
        new TowerBootstrapSyntax(
            "bootstrap-pr-1",
            "open",
            "Godel boundary.",
            "sha256:fc2ee6be0dd3cabb9b6a9118592671c9d5a81f691b7b4ad07674d9c3037ce262",
            "f3f471846dd81cfcc39ecaa386966fcf0b058464",
            1,
            "ASSUMED-UNVERIFIED"));

    private static RepositorySnapshot Snapshot()
    {
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [C0CeremonyProjection.CliApplicationPath] = "// cli\n",
            [C0CeremonyProjection.ProductionEnvironmentPath] =
                "// environment\n",
            [C0CeremonyProjection.CheckCommandPath] = "// check command\n",
            [C0CeremonyProjection.GitRepositoryGatewaySourcePath] =
                "// git gateway\n",
            [C0CeremonyProjection.GitRepositoryGatewayFrozenLedgerSourcePath] =
                "// frozen git gateway\n",
            [C0CeremonyProjection.ProgramPath] = "// program\n",
            [C0CeremonyProjection.ProjectionSourcePath] =
                "// projection\n",
            [C0CeremonyProjection.ActualValidatorPath] =
                "// actual validator\n",
            [C0CeremonyProjection.TowerManifestSourcePath] =
                "// manifest\n",
            [C0CeremonyProjection.TowerParserSourcePath] =
                "// parser\n",
            [NestedControllerPath] = "// controller\n",
            [NestedCorpusSourcePath] = "// corpus source\n",
            [NestedCorpusDataPath] = "[[cases]]\n",
            [C0CeremonyProjection.FixtureRegistryPath] = "schema_version: 1\n",
            [C0CeremonyProjection.ValuesKernelDataPath] = "schema_version = 1\n",
            [C0CeremonyProjection.GateWiringPath] = "#!/bin/bash\n",
            [C0CeremonyProjection.LocalGateWiringPath] = "#!/bin/bash\n",
            [C0CeremonyProjection.LeanReportPairPath] = "#!/bin/bash\n",
            [C0CeremonyProjection.LeanInspectorScriptPath] = "#!/bin/bash\n",
            [C0CeremonyProjection.LeanInspectorSourcePath] = "def main := pure ()\n",
            [C0CeremonyProjection.CertificatePath] = "{}\n",
            [FrozenLedgerChangeClassifier.LedgerPath] =
                "{\"event_hash\":\"sha256:fc2ee6be0dd3cabb9b6a9118592671c9d5a81f691b7b4ad07674d9c3037ce262\",\"event_type\":\"Genesis\"}\n",
        };
        var raw = RawRepositorySnapshot.Create(files.Select(static item =>
            RawRepositoryEntry.FromText(item.Key, item.Value)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }
}
