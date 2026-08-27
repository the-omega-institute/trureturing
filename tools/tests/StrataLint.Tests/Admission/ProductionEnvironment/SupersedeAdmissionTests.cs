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
    public void PinBumpReportsInfrastructureFailureWhenMaterialArchiveIsMissingAndUsed()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = CreatePinBumpFixture([], []);
        AddSupersedeEvents(fixture);
        var candidateReport = WriteCandidateReport(temporary, fixture);
        File.Delete(RawLeanReportArtifact.MaterialsPath(candidateReport));
        var environment = new ProductionCliEnvironment(
            "/repo",
            PinBumpGateway(fixture),
            new FakeLeanReportSource(null));
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["check", "--candidate-lean-report", candidateReport],
            environment,
            console);

        Assert.Equal(2, exitCode);
        Assert.Contains(
            "INFRASTRUCTURE_FAILURE Lean statement material archive is missing",
            console.Error,
            StringComparison.Ordinal);
    }

    [Fact]
    public void PinBumpWithLargerStandardSupersedeClosureIsAccepted()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = CreatePinBumpFixture(["propext"], ["Classical.choice", "propext"]);
        AddSupersedeEvents(fixture);

        var outcome = CheckPinBump(temporary, fixture, PinBumpGateway(fixture));

        Assert.IsType<AdmissionOutcome.ProtectedSurfaceChange>(outcome);
    }

    [Fact]
    public void PinBumpWithIncomparableStandardSupersedeClosureIsAccepted()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = CreatePinBumpFixture(["propext"], ["Classical.choice"]);
        AddSupersedeEvents(fixture);

        var outcome = CheckPinBump(temporary, fixture, PinBumpGateway(fixture));

        Assert.IsType<AdmissionOutcome.ProtectedSurfaceChange>(outcome);
    }

    [Fact]
    public void PinBumpWithNonStandardSupersedeClosureIsRejected()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = CreatePinBumpFixture([], []);
        AddSupersedeEvents(fixture);
        InjectNonStandardSupersedeAxiom(fixture);

        var outcome = CheckPinBump(temporary, fixture, PinBumpGateway(fixture));

        AssertSupersedeRejection(outcome, "standard");
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
    public void PinBumpWithUnknownRecordedClosureIsAccepted()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = CreatePinBumpFixture([], []);
        AddSupersedeEvents(fixture);
        RemoveRecordedClosure(fixture, RuleFixture.RingPath);

        var outcome = CheckPinBump(temporary, fixture, PinBumpGateway(fixture));

        Assert.IsType<AdmissionOutcome.ProtectedSurfaceChange>(outcome);
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

    [Fact]
    public void ProductionCheckRejectsSupersedeWhenARepositoryImportChanged()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var dependencyPath = FrozenLedgerTestData.PathFor("BackfillTarget");
        const string dependencyModule = "D5.S0.Carrier.BackfillTarget";
        fixture.Reports[RuleFixture.RingPath] = RingReport(
            [],
            "Nat",
            [dependencyModule]);
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
        fixture.Files[dependencyPath] += "-- imported meaning changed\n";
        fixture.Reports[RuleFixture.RingPath] = RingReport(
            [],
            "ambiently-weakened-imported-expression",
            [dependencyModule]);
        AddSupersedeEvents(fixture);
        var eventChanges = AddedLedgerPaths(fixture)
            .Select(static path => (path, RawChangeKind.Added));
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.CreateWithKinds(
                new[]
                {
                    ("lean-toolchain", RawChangeKind.Modified),
                    (dependencyPath, RawChangeKind.Modified),
                }.Concat(eventChanges)),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline));

        var outcome = CheckPinBump(temporary, fixture, gateway);

        AssertSupersedeRejection(outcome, "import closure");
    }

    [Fact]
    public void ProductionCheckRejectsWeakerMeaningFromAnUntrackedExternalImport()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath]
            .Replace("def goldenRing", "import External.Foo\n\ndef goldenRing", StringComparison.Ordinal);
        fixture.Reports[RuleFixture.RingPath] = RingReport(
            [],
            "Nat.Prime 2",
            ["External.Foo"]);
        fixture.Baseline[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath];
        fixture.BaselineReports[RuleFixture.RingPath] = fixture.Reports[RuleFixture.RingPath];
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
        fixture.Reports[RuleFixture.RingPath] = RingReport([], "True", ["External.Foo"]);
        AddSupersedeEvents(fixture);

        var outcome = CheckPinBump(temporary, fixture, PinBumpGateway(fixture));

        AssertSupersedeRejection(outcome, "external import");
    }

    [Fact]
    public void ProductionCheckRejectsWeakerMeaningFromPinnedExternalImportWithUnchangedGitRevision()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        const string baselineManifest =
            "{\"packages\":[{\"name\":\"mathlib\",\"type\":\"git\",\"rev\":\"abc123\"}]}\n";
        fixture.Files[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath]
            .Replace("def goldenRing", "import Mathlib.Foo\n\ndef goldenRing", StringComparison.Ordinal);
        fixture.Reports[RuleFixture.RingPath] = RingReport(
            [],
            "Nat.Prime 2",
            ["Mathlib.Foo"]);
        fixture.Baseline[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath];
        fixture.BaselineReports[RuleFixture.RingPath] = fixture.Reports[RuleFixture.RingPath];
        _ = AddFrozenLedger(fixture, baselineManifest);
        foreach (var item in fixture.Files)
        {
            fixture.Baseline[item.Key] = item.Value;
        }
        foreach (var item in fixture.Reports)
        {
            fixture.BaselineReports[item.Key] = item.Value;
        }

        fixture.Files["lean-toolchain"] = "leanprover/lean4:v4.25.0\n";
        fixture.Reports[RuleFixture.RingPath] = RingReport([], "True", ["Mathlib.Foo"]);
        AddSupersedeEvents(fixture);

        var outcome = CheckPinBump(temporary, fixture, PinBumpGateway(fixture));

        AssertSupersedeRejection(outcome, "trivial truth");
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

    private static LeanFileReport RingReport(
        ImmutableArray<string> axioms,
        string statementMaterial = "Nat",
        ImmutableArray<string> imports = default) => new(
        imports.IsDefault ? [] : imports,
        [new LeanDeclaration("goldenRing", "def", statementMaterial, axioms)]);

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
                    && root.GetProperty("payload").GetProperty("input")
                        .GetProperty("descriptor_selector").GetString() == nodePath;
            }).Key;
        var root = JsonNode.Parse(fixture.Files[freezePath])!.AsObject();
        root["payload"]!.AsObject().Remove("axiom_closure");
        var withoutClosure = root.ToJsonString() + "\n";
        fixture.Files[freezePath] = withoutClosure;
        fixture.Baseline[freezePath] = withoutClosure;
    }

    private static void InjectNonStandardSupersedeAxiom(RuleFixture fixture)
    {
        foreach (var path in AddedLedgerPaths(fixture)
                     .Where(path => EventType(fixture.Files[path]) == FrozenLedger.SupersedeEventType)
                     .ToArray())
        {
            var root = JsonNode.Parse(fixture.Files[path])!.AsObject();
            root["payload"]!.AsObject()["axiom_closure"]!.AsArray()
                .Add("random.nonstandard_axiom");
            var payload = JsonSerializer.Deserialize<JsonElement>(
                root["payload"]!.ToJsonString());
            var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
                FrozenLedger.SupersedeEventType,
                payload);
            var identity = FrozenLedgerCanonicalWriter.EventIdentity(
                FrozenLedger.SupersedeEventType,
                payload,
                encoded.Hash);
            fixture.Files.Remove(path);
            fixture.Files[FrozenLedgerChangeClassifier.AcceptedPath(identity)] =
                Encoding.UTF8.GetString(encoded.Bytes.AsSpan());
        }
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
        var matching = rejected.Diagnostics
            .Where(static item => item.RuleId == RuleId.CreateKnown(8))
            .ToArray();
        Assert.True(
            matching.Length == 1,
            string.Join("\n", rejected.Diagnostics.Select(static item => item.Render())));
        var diagnostic = matching[0];
        Assert.Contains(message, diagnostic.Message, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("delta witness:", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("lean-toolchain", diagnostic.Message, StringComparison.Ordinal);
    }
}
