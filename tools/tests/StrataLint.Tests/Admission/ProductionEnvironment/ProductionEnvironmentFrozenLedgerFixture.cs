using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    private static RuleFixture TrustedFrozenFixtureWithLedger(
        out FrozenLedgerConsistent baselineLedger)
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        baselineLedger = AddFrozenLedger(fixture);
        foreach (var item in fixture.Files)
        {
            fixture.Baseline[item.Key] = item.Value;
        }
        foreach (var item in fixture.Reports)
        {
            fixture.BaselineReports[item.Key] = item.Value;
        }

        return fixture;
    }

    private static string AddIncompleteReattest(RuleFixture fixture)
    {
        var payload = JsonSerializer.SerializeToElement(new
        {
            frozen_node_id = "sha256:" + new string('9', 64),
            input = new
            {
                base_commit_oid = FrozenLedgerTestData.GitOid('a'),
                base_tree_oid = FrozenLedgerTestData.GitOid('b'),
                descriptor_blob_oid = FrozenLedgerTestData.GitBlobOid(
                    fixture.Files[RuleFixture.RingPath]),
                descriptor_selector = RuleFixture.RingPath,
                materializer = "repository-snapshot-v1",
                supporting_blob_oids = Array.Empty<string>(),
            },
        });
        var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent("Reattest", payload);
        var identity = FrozenLedgerCanonicalWriter.EventIdentity(
            "Reattest",
            payload,
            encoded.Hash);
        var path = FrozenLedgerChangeClassifier.AcceptedPath(identity);
        fixture.Files[path] = Encoding.UTF8.GetString(encoded.Bytes.AsSpan());
        return path;
    }

    private static string AddMatchingReattest(
        RuleFixture fixture,
        FrozenLedgerConsistent baselineLedger,
        out ImmutableArray<byte> reattestedLedger)
    {
        var candidateCatalog = BuildFrozenCatalog(fixture.Files, fixture.Reports);
        reattestedLedger = FrozenLedgerGenerator.AppendReattestation(
            baselineLedger,
            candidateCatalog);
        SetLedger(fixture.Files, Encoding.UTF8.GetString(reattestedLedger.AsSpan()));
        return Assert.Single(AddedLedgerPaths(fixture), path => EventType(fixture.Files[path]) == "Reattest");
    }

    private static void DriftEnvironmentAndStatementIdentity(RuleFixture fixture, string statementType)
    {
        fixture.Files["lean-toolchain"] = "leanprover/lean4:v4.25.0\n";
        fixture.Reports[RuleFixture.RingPath] = new LeanFileReport(
            [],
            [new LeanDeclaration("goldenRing", "def", statementType, [])]);
    }

    private static string AddEnvironmentRecoordinate(
        RuleFixture fixture,
        FrozenLedgerConsistent baselineLedger,
        LeanFileReport eventReport)
    {
        _ = baselineLedger;
        var eventReports = new Dictionary<string, LeanFileReport>(fixture.Reports, StringComparer.Ordinal)
        {
            [RuleFixture.RingPath] = eventReport,
        };
        var candidateCatalog = BuildFrozenCatalog(fixture.Files, eventReports);
        var baseView = FrozenLedgerBaseViewReader.Read(Decode(Snapshot(fixture.Baseline)));
        var oldEnvironment = FrozenEnvironment(fixture.Baseline);
        var newEnvironment = FrozenEnvironment(fixture.Files);
        var oldPins = FrozenPins(oldEnvironment);
        var newPins = FrozenPins(newEnvironment);
        string? ringEventPath = null;
        foreach (var active in baseView.ActiveByPath.Values.OrderBy(
            static entry => entry.Material.RepoPath.Value,
            StringComparer.Ordinal))
        {
            var modulePath = active.Material.RepoPath;
            var candidate = candidateCatalog.ByPath[modulePath];
            var newReport = eventReports[modulePath.Value];
            var oldReport = fixture.BaselineReports[modulePath.Value];
            var oldInput = active.Payload.Input with
            {
                SupportingBlobOids = EnvironmentOids(oldPins),
            };
            var newInput = FrozenLedgerCanonicalWriter.FreezePayload(newEnvironment, candidate).Input with
            {
                SupportingBlobOids = EnvironmentOids(newPins),
            };
            var payload = new FrozenEnvironmentRecoordinatePayload(
                active.Payload.CaseId,
                candidate.DeclarationStatementIds,
                active.Material.DeclarationStatementIds,
                newPins,
                oldPins,
                FrozenLedger.EnvironmentRecoordinateUnprovedEquivalence,
                nameof(TruthState.Closed),
                candidate.AxiomClosure,
                candidate.FrozenNodeId,
                newReport.Imports.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToImmutableArray(),
                newInput,
                candidate.PrerequisiteFrozenNodeIds,
                candidate.StatementId,
                candidate.WitnessId,
                oldReport.Declarations.SelectMany(static declaration => declaration.Axioms)
                    .Distinct(StringComparer.Ordinal)
                    .Order(StringComparer.Ordinal)
                    .ToImmutableArray(),
                active.Material.FrozenNodeId,
                oldReport.Imports.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToImmutableArray(),
                oldInput,
                active.Material.PrerequisiteFrozenNodeIds,
                active.Material.StatementId,
                active.Material.WitnessId,
                active.LastAttestationEventHash,
                "sha256:" + Convert.ToHexStringLower(SHA256.HashData(
                    Encoding.UTF8.GetBytes(fixture.Files[modulePath.Value]))));
            var element = FrozenLedgerCanonicalWriter.EnvironmentRecoordinateElement(payload);
            var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
                FrozenLedger.EnvironmentRecoordinateEventType,
                element);
            var identity = FrozenLedgerCanonicalWriter.EventIdentity(
                FrozenLedger.EnvironmentRecoordinateEventType,
                element,
                encoded.Hash);
            var path = FrozenLedgerChangeClassifier.AcceptedPath(identity);
            fixture.Files[path] = Encoding.UTF8.GetString(encoded.Bytes.AsSpan());
            if (modulePath.Value == RuleFixture.RingPath)
            {
                ringEventPath = path;
            }
        }

        Assert.NotNull(ringEventPath);
        return ringEventPath;
    }

    private static FrozenMaterialCatalog BuildFrozenCatalog(
        IReadOnlyDictionary<string, string> files,
        IReadOnlyDictionary<string, LeanFileReport> reports)
    {
        var (snapshot, lean, dag) = BuildState(files, reports);
        var attestations = dag.Nodes
            .Where(static node => node.State is TruthState.Closed && node.ModuleName is not null)
            .Select(node => new FrozenModuleAttestation(
                node.RepoPath,
                FrozenLedgerTestData.GitBlobOid(files[node.RepoPath.Value]))
            {
                BaseCommitOid = FrozenLedgerTestData.GitOid('a'),
                BaseTreeOid = FrozenLedgerTestData.GitOid('b'),
            });
        return Assert.IsType<FrozenMaterialOutcome.Accepted>(
            FrozenContentAddress.Build(snapshot, lean, dag, FrozenEnvironment(files), attestations)).Capability;
    }

    private static FrozenEnvironmentAttestation FrozenEnvironment(
        IReadOnlyDictionary<string, string> files) => new(
            FrozenLedgerTestData.GitOid('a'),
            FrozenLedgerTestData.GitOid('b'),
            FrozenLedgerTestData.GitBlobOid(files["lean-toolchain"]),
            FrozenLedgerTestData.GitBlobOid(files["lake-manifest.json"]))
        {
            LakefilePath = "lakefile.toml",
            LakefileBlobOid = FrozenLedgerTestData.GitBlobOid(files["lakefile.toml"]),
        };

    private static FrozenEnvironmentPins FrozenPins(FrozenEnvironmentAttestation environment) => new(
        environment.LakeManifestBlobOid,
        environment.LakefileBlobOid!,
        RepoPath.CreateKnown(environment.LakefilePath!),
        environment.LeanToolchainBlobOid);

    private static ImmutableArray<string> EnvironmentOids(FrozenEnvironmentPins environment) =>
        new[]
        {
            environment.LakeManifestBlobOid,
            environment.LakefileBlobOid,
            environment.LeanToolchainBlobOid,
        }.Order(StringComparer.Ordinal).ToImmutableArray();

    private static string EventType(string contents)
    {
        using var document = JsonDocument.Parse(contents);
        return document.RootElement.GetProperty("event_type").GetString()!;
    }
}
