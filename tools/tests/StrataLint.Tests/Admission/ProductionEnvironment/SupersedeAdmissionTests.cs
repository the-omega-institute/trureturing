using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void PinBumpWithValidSupersedeEventsIsAccepted()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = CreatePinBumpFixture([], []);
        AddSupersedeEvents(fixture);
        var gateway = PinBumpGateway(fixture);

        var outcome = CheckPinBump(temporary, fixture, gateway);

        Assert.IsType<AdmissionOutcome.ProtectedSurfaceChange>(outcome);
    }

    [Fact]
    public void PinBumpWithLargerSupersedeClosureIsRejected()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = CreatePinBumpFixture(["propext"], ["Classical.choice", "propext"]);
        AddSupersedeEvents(fixture);

        var outcome = CheckPinBump(temporary, fixture, PinBumpGateway(fixture));

        AssertSupersedeRejection(outcome, "axiom closure");
    }

    [Fact]
    public void PinBumpWithIncomparableSupersedeClosureIsRejected()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = CreatePinBumpFixture(["propext"], ["Classical.choice"]);
        AddSupersedeEvents(fixture);

        var outcome = CheckPinBump(temporary, fixture, PinBumpGateway(fixture));

        AssertSupersedeRejection(outcome, "axiom closure");
    }

    [Fact]
    public void PinBumpWithMissingSupersedeIsRejected()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = CreatePinBumpFixture([], []);
        AddSupersedeEvents(fixture, skipPath: RuleFixture.RingPath);

        var outcome = CheckPinBump(temporary, fixture, PinBumpGateway(fixture));

        AssertSupersedeRejection(outcome, "missing a Supersede event");
    }

    [Fact]
    public void PinBumpWithUnknownRecordedClosureIsRejected()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = CreatePinBumpFixture([], []);
        AddSupersedeEvents(fixture);
        RemoveRecordedClosure(fixture, RuleFixture.RingPath);

        var outcome = CheckPinBump(temporary, fixture, PinBumpGateway(fixture));

        AssertSupersedeRejection(outcome, "recorded axiom closure is unknown");
    }

    [Fact]
    public void SupersedeAdmissionValidatesOnlyCandidateReferencesAndNeverOldEnvironment()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = CreatePinBumpFixture([], []);
        AddSupersedeEvents(fixture);
        var gateway = PinBumpGateway(fixture);

        var outcome = CheckPinBump(temporary, fixture, gateway);

        Assert.IsType<AdmissionOutcome.ProtectedSurfaceChange>(outcome);
        var references = Assert.Single(gateway.FrozenReferenceValidations);
        var supersedeCount = AddedLedgerPaths(fixture).Count(path =>
            EventType(fixture.Files[path]) == FrozenLedger.SupersedeEventType);
        Assert.Equal(supersedeCount, references.Inputs.Length);
        Assert.Equal(supersedeCount, references.EnvironmentReferences.Length);
        var candidateToolchain = FrozenLedgerTestData.GitBlobOid(fixture.Files["lean-toolchain"]);
        var oldToolchain = FrozenLedgerTestData.GitBlobOid(fixture.Baseline["lean-toolchain"]);
        Assert.All(
            references.EnvironmentReferences,
            reference => Assert.Equal(candidateToolchain, reference.Environment.LeanToolchainBlobOid));
        Assert.DoesNotContain(
            references.EnvironmentReferences,
            reference => reference.Environment.LeanToolchainBlobOid == oldToolchain);
    }

    private static RuleFixture CreatePinBumpFixture(
        ImmutableArray<string> baselineAxioms,
        ImmutableArray<string> candidateAxioms)
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Reports[RuleFixture.RingPath] = RingReport(baselineAxioms);
        _ = AddFrozenLedger(fixture);
        foreach (var item in fixture.Files)
        {
            fixture.Baseline[item.Key] = item.Value;
        }
        foreach (var item in fixture.Reports)
        {
            fixture.BaselineReports[item.Key] = item.Value;
        }

        fixture.Files["lean-toolchain"] = "leanprover/lean4:v4.25.0\n";
        fixture.Reports[RuleFixture.RingPath] = RingReport(candidateAxioms);
        return fixture;
    }

    private static LeanFileReport RingReport(ImmutableArray<string> axioms) => new(
        [],
        [new LeanDeclaration("goldenRing", "def", "Nat", axioms)]);

    private static void AddSupersedeEvents(RuleFixture fixture, string? skipPath = null)
    {
        var baseView = FrozenLedgerBaseViewReader.Read(Decode(Snapshot(fixture.Baseline)));
        var candidateCatalog = BuildFrozenCatalog(fixture.Files, fixture.Reports);
        var environment = FrozenPins(FrozenEnvironment(fixture.Files));
        foreach (var active in baseView.ActiveByPath.Values.OrderBy(
            static entry => entry.Material.RepoPath.Value,
            StringComparer.Ordinal))
        {
            if (active.Material.RepoPath.Value == skipPath)
            {
                continue;
            }

            var candidate = candidateCatalog.ByPath[active.Material.RepoPath];
            var input = FrozenLedgerCanonicalWriter.FreezePayload(
                candidateCatalog.Environment,
                candidate).Input with
            {
                SupportingBlobOids = EnvironmentOids(environment),
            };
            var payload = new FrozenSupersedePayload(
                candidate.AxiomClosure,
                active.Payload.CaseId,
                candidate.DeclarationStatementIds,
                environment,
                candidate.FrozenNodeId,
                input,
                candidate.PrerequisiteFrozenNodeIds,
                active.LastAttestationEventHash,
                candidate.StatementId,
                candidate.WitnessId);
            var element = FrozenLedgerCanonicalWriter.SupersedeElement(payload);
            var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
                FrozenLedger.SupersedeEventType,
                element);
            var identity = FrozenLedgerCanonicalWriter.EventIdentity(
                FrozenLedger.SupersedeEventType,
                element,
                encoded.Hash);
            fixture.Files[FrozenLedgerChangeClassifier.AcceptedPath(identity)] =
                Encoding.UTF8.GetString(encoded.Bytes.AsSpan());
        }
    }

    private static void RemoveRecordedClosure(RuleFixture fixture, string nodePath)
    {
        var freezePath = fixture.Files
            .Where(static item => FrozenLedgerChangeClassifier.IsAcceptedEventPath(item.Key))
            .Single(item =>
            {
                using var document = JsonDocument.Parse(item.Value);
                var root = document.RootElement;
                return root.GetProperty("event_type").GetString() == "Freeze"
                    && root.GetProperty("payload").GetProperty("node_path").GetString() == nodePath;
            }).Key;
        var root = JsonNode.Parse(fixture.Files[freezePath])!.AsObject();
        root["payload"]!.AsObject().Remove("axiom_closure");
        var withoutClosure = root.ToJsonString() + "\n";
        fixture.Files[freezePath] = withoutClosure;
        fixture.Baseline[freezePath] = withoutClosure;
    }

    private static FakeRepositoryGateway PinBumpGateway(RuleFixture fixture)
    {
        var eventChanges = AddedLedgerPaths(fixture)
            .Select(static path => (path, RawChangeKind.Added));
        return new FakeRepositoryGateway(
            RawChangeSet.CreateWithKinds(
                new[] { ("lean-toolchain", RawChangeKind.Modified) }.Concat(eventChanges)),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline));
    }

    private static AdmissionOutcome CheckPinBump(
        TemporaryDirectory temporary,
        RuleFixture fixture,
        FakeRepositoryGateway gateway)
    {
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null));
        return environment.Check(
            ["--candidate-lean-report", WriteCandidateReport(temporary, fixture)]);
    }

    private static void AssertSupersedeRejection(AdmissionOutcome outcome, string message)
    {
        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var diagnostic = Assert.Single(
            rejected.Diagnostics.Where(static item => item.RuleId == RuleId.CreateKnown(8)));
        Assert.Contains(message, diagnostic.Message, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("delta witness:", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("lean-toolchain", diagnostic.Message, StringComparison.Ordinal);
    }
}
