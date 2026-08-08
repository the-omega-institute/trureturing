using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class C0CeremonyProjectionTests
{
    private const string NestedControllerPath =
        "Meta/StrataLint/StrataLint.Cli/Conservative/Nested/Worker.cs";

    [Fact]
    public void ProductionPolicyDiscoversNestedAnchorsWithoutReadingTower()
    {
        var anchors = C0CeremonyProjection.DiscoverAnchors(Snapshot());

        Assert.Contains(anchors, item => item is
        {
            Kind: C0AnchorKind.Controller,
            Path: NestedControllerPath,
        });
        Assert.DoesNotContain(
            anchors,
            static item => item.Path == RepositoryRules.TowerManifestPath);
        Assert.Single(anchors, static item => item.Kind == C0AnchorKind.GateWiring);
    }

    [Fact]
    public void MissingNamedAnchorStillFailsCustodianProjection()
    {
        var snapshot = Snapshot(includeGate: false);

        Assert.False(C0CeremonyProjection.TryCreateAnchorCustodianReferences(snapshot, out _));
    }

    [Fact]
    public void FrozenTrustRootMatchesCertificateBytesAndCandidateTree()
    {
        var snapshot = Snapshot();
        var certificate = snapshot.Files.Values.Single(static file =>
            file.Path.Value == C0CeremonyProjection.CertificatePath).RawBytes;
        using var document = JsonDocument.Parse(certificate.ToArray());
        var tree = document.RootElement.GetProperty("candidate").GetProperty("tree_oid").GetString()!;
        var digest = Convert.ToHexStringLower(SHA256.HashData(certificate.AsSpan()));
        var members = Members(digest, tree["git-sha1:".Length..]);

        Assert.True(C0CeremonyProjection.HasCanonicalShape(members));
        Assert.True(C0CeremonyProjection.TrustRootMatchesSnapshot(members, snapshot, out var reason), reason);
    }

    [Fact]
    public void FrozenTrustRootRejectsAChangedCertificateAddress()
    {
        var snapshot = Snapshot();
        var members = Members(new string('f', 64), new string('a', 40));

        Assert.False(C0CeremonyProjection.TrustRootMatchesSnapshot(members, snapshot, out var reason));
        Assert.Contains("certificate address", reason, StringComparison.Ordinal);
    }

    private static ImmutableArray<string> Members(string digest, string tree) =>
    [
        "phase1-protected-content-admission",
        "phase2-dual-harness-conservative-extension",
        "c0/ceremony-commit convention/this-pr-merge-commit",
        $"c0/inaugural-certificate sha256/{digest} {C0CeremonyProjection.CertificatePath}",
        $"c0/preimage-tree git-tree/{tree}",
    ];

    private static RepositorySnapshot Snapshot(bool includeGate = true)
    {
        var certificate = StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(new
        {
            candidate = new { tree_oid = "git-sha1:" + new string('a', 40) },
            schema = "stratalint-conservative-certificate-v1",
        }));
        var files = new Dictionary<string, ImmutableArray<byte>>(StringComparer.Ordinal)
        {
            [C0CeremonyProjection.CliApplicationPath] = Bytes("// cli\n"),
            [C0CeremonyProjection.ProductionEnvironmentPath] = Bytes("// environment\n"),
            [C0CeremonyProjection.GitRepositoryGatewaySourcePath] = Bytes("// git\n"),
            [C0CeremonyProjection.GitRepositoryGatewayFrozenLedgerSourcePath] = Bytes("// frozen\n"),
            [C0CeremonyProjection.FrozenEvidenceResolverSourcePath] = Bytes("// evidence\n"),
            [C0CeremonyProjection.ProgramPath] = Bytes("// program\n"),
            [C0CeremonyProjection.ProjectionSourcePath] = Bytes("// projection\n"),
            [C0CeremonyProjection.ActualValidatorPath] = Bytes("// validator\n"),
            [C0CeremonyProjection.TowerManifestSourcePath] = Bytes("// manifest\n"),
            [C0CeremonyProjection.TowerParserSourcePath] = Bytes("// parser\n"),
            [C0CeremonyProjection.FixtureRegistryPath] = Bytes("schema_version: 1\n"),
            [C0CeremonyProjection.ValuesKernelDataPath] = Bytes("schema_version = 1\n"),
            [C0CeremonyProjection.LocalGateWiringPath] = Bytes("#!/bin/bash\n"),
            [C0CeremonyProjection.LeanReportPairPath] = Bytes("#!/bin/bash\n"),
            [C0CeremonyProjection.LeanInspectorScriptPath] = Bytes("#!/bin/bash\n"),
            [C0CeremonyProjection.LeanInspectorSourcePath] = Bytes("def main := pure ()\n"),
            [NestedControllerPath] = Bytes("// nested\n"),
            [C0CeremonyProjection.CertificatePath] = certificate,
        };
        if (includeGate) files[C0CeremonyProjection.GateWiringPath] = Bytes("#!/bin/bash\n");
        var raw = RawRepositorySnapshot.Create(files.Select(static item =>
            new RawRepositoryEntry(item.Key, item.Value)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

    private static ImmutableArray<byte> Bytes(string value) =>
        ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(value));
}
