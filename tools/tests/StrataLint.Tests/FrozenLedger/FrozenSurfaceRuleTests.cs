using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class FrozenSurfaceRuleTests
{
    private const string FrozenPath = RuleFixture.RingPath;
    private const string OtherPath = RuleFixture.BlueprintPath;
    // Derived once by independently canonicalizing the RuleFixture raw report's
    // goldenRing/def/Nat declaration and the module-statement-v1 material.
    private const string ExpectedFrozenModuleStatementPin =
        "sha256:3d2b9bf06c5fb9076c8206428611c597cc723e59b64f5415e7dae6049ee954e2";
    private static readonly string FrozenStatePathValue =
        FrozenStatePath.FromModulePath(RepoPath.CreateKnown(FrozenPath)).Value;
    [Theory]
    [InlineData(RawChangeKind.Modified)]
    [InlineData(RawChangeKind.Deleted)]
    public void Sl008RejectsChangedHearts(RawChangeKind kind)
    {
        var fixture = new RuleFixture();
        if (kind == RawChangeKind.Deleted)
        {
            fixture.Files.Remove(RuleFixture.HeartsPath);
            fixture.Reports.Remove(RuleFixture.HeartsPath);
        }

        var evaluation = Evaluate(fixture, (RuleFixture.HeartsPath, kind));

        var diagnostic = Assert.Single(evaluation.Diagnostics);
        Assert.Equal(RuleFixture.HeartsPath, diagnostic.Path);
        Assert.Contains("SL-022", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008AllowsUnchangedHearts()
    {
        var fixture = new RuleFixture();

        var evaluation = Evaluate(fixture);

        Assert.Empty(evaluation.Diagnostics);
    }

    [Theory]
    [InlineData(RawChangeKind.Modified)]
    [InlineData(RawChangeKind.Deleted)]
    public void Sl008AllowsSnapshotReplacementOfAcceptedEventFragment(RawChangeKind kind)
    {
        var fixture = FrozenFixture(out var eventPath);
        if (kind == RawChangeKind.Deleted)
        {
            fixture.Files.Remove(eventPath);
        }

        var evaluation = Evaluate(fixture, (eventPath, kind));

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl008AllowsAddedAcceptedEventFragment()
    {
        var fixture = FrozenFixture(out var eventPath);

        var evaluation = Evaluate(fixture, (eventPath, RawChangeKind.Added));

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl008IgnoresModifiedNonFrozenModule()
    {
        var fixture = FrozenFixture(out _);

        var evaluation = Evaluate(fixture, (OtherPath, RawChangeKind.Modified));

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl008RejectsStatePinThatDiffersFromTheCurrentReport()
    {
        var fixture = new RuleFixture();
        var actual = StatementId.Create(ExpectedFrozenModuleStatementPin);
        var stored = StatementId.Create("sha256:" + new string('f', 64));
        Assert.NotEqual(stored, actual);
        AddState(fixture, FrozenPath, stored);

        var diagnostic = Assert.Single(
            Evaluate(fixture, (FrozenStatePathValue, RawChangeKind.Added)).Diagnostics);

        Assert.Equal($"frozen state {FrozenStatePathValue}", diagnostic.Path);
        Assert.Contains(FrozenPath, diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains($"stored={stored.Value}", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains($"actual={actual.Value}", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008RejectsStateWhoseModuleDoesNotExist()
    {
        var fixture = new RuleFixture();
        const string missingModule = "D5/S0/Carrier/Missing.lean";
        var statePath = FrozenStatePath.FromModulePath(RepoPath.CreateKnown(missingModule)).Value;
        fixture.Files[statePath] = StateText(StatementId.Create("sha256:" + new string('1', 64)));

        var diagnostic = Assert.Single(
            Evaluate(fixture, (statePath, RawChangeKind.Added)).Diagnostics);

        Assert.Equal($"SL-008 frozen state {statePath}: module {missingModule} does not exist", diagnostic.Render());
    }

    [Fact]
    public void Sl008C1RequiresACanonicalRepositoryLeanModulePath()
    {
        var fixture = new RuleFixture();
        const string statePath = "Golden/Frozen/state/d5/S0/Carrier/Ring.lean.json";
        fixture.Files[statePath] = StateText(StatementId.Create("sha256:" + new string('1', 64)));

        var diagnostic = Assert.Single(
            Evaluate(fixture, (statePath, RawChangeKind.Added)).Diagnostics);

        Assert.Equal(
            $"SL-008 frozen state {statePath}: path must encode exactly one canonical repository Lean module",
            diagnostic.Render());
    }

    [Fact]
    public void Sl008C2RequiresTheClosedStateSchema()
    {
        var fixture = new RuleFixture();
        fixture.Files[FrozenStatePathValue] =
            $"{{\"statement_id\":\"{ExpectedFrozenModuleStatementPin}\",\"history\":[]}}\n";

        var diagnostic = Assert.Single(
            Evaluate(fixture, (FrozenStatePathValue, RawChangeKind.Added)).Diagnostics);

        Assert.Equal($"frozen state {FrozenStatePathValue}", diagnostic.Path);
        Assert.Contains(
            "record keys must be exactly {statement_id}",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008RejectsStateWhoseModuleIsNotClosed()
    {
        var fixture = new RuleFixture();
        fixture.SetRingDeclaration("openRing", "axiom", "fixtureAxiom");
        AddState(fixture, FrozenPath, ModuleStatementId(fixture, FrozenPath));

        var diagnostic = Assert.Single(
            Evaluate(fixture, (FrozenStatePathValue, RawChangeKind.Added)).Diagnostics);

        Assert.Equal(
            $"SL-008 frozen state {FrozenStatePathValue}: module {FrozenPath} has TruthState=Tail, expected Closed",
            diagnostic.Render());
    }

    [Fact]
    public void Sl008DoesNotCompareAcceptedFreezePinsWithCurrentState()
    {
        var fixture = new RuleFixture();
        var statePin = ModuleStatementId(fixture, FrozenPath);
        var eventPin = StatementId.Create("sha256:" + new string('e', 64));
        AddState(fixture, FrozenPath, statePin);
        _ = AddFreeze(fixture, FrozenPath, eventPin);

        var evaluation = Evaluate(fixture, (FrozenStatePathValue, RawChangeKind.Added));

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl008AllowsHeaderOrCommentChangesWhenTheModulePinIsUnchanged()
    {
        var fixture = new RuleFixture();
        var pin = StatementId.Create(ExpectedFrozenModuleStatementPin);
        AddState(fixture, FrozenPath, pin, includeInBaseline: true);
        _ = AddFreeze(fixture, FrozenPath, pin);
        fixture.Files[FrozenPath] = fixture.Files[FrozenPath].Replace(
            "anchors: []",
            "anchors: [mathlib/module/Nat]",
            StringComparison.Ordinal);
        var freshPin = ModuleStatementId(fixture, FrozenPath);
        Assert.Equal(pin, freshPin);

        var evaluation = Evaluate(fixture, (FrozenPath, RawChangeKind.Modified));

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl008RejectsStatementChangeWhenCurrentStateRetainsTheOldPin()
    {
        var fixture = new RuleFixture();
        var stored = ModuleStatementId(fixture, FrozenPath);
        AddState(fixture, FrozenPath, stored, includeInBaseline: true);
        fixture.Files[FrozenPath] = fixture.Files[FrozenPath].Replace(
            "def goldenRing : Nat := 0",
            "def goldenRing : Int := 0",
            StringComparison.Ordinal);
        ChangeStatement(fixture, FrozenPath, "Int");
        var actual = ModuleStatementId(fixture, FrozenPath);
        Assert.NotEqual(stored, actual);

        var diagnostic = Assert.Single(
            Evaluate(fixture, (FrozenPath, RawChangeKind.Modified)).Diagnostics);

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal($"frozen state {FrozenStatePathValue}", diagnostic.Path);
        Assert.Contains($"selector {FrozenPath}", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains($"stored={stored.Value}", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains($"actual={actual.Value}", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008AllowsStatementAndStateToMoveTogetherAndObservesThePinChange()
    {
        var fixture = new RuleFixture();
        var oldPin = ModuleStatementId(fixture, FrozenPath);
        AddState(fixture, FrozenPath, oldPin, includeInBaseline: true);
        ChangeStatement(fixture, FrozenPath, "Int");
        var newPin = ModuleStatementId(fixture, FrozenPath);
        AddState(fixture, FrozenPath, newPin);

        var diagnostic = Assert.Single(Evaluate(
            fixture,
            (FrozenPath, RawChangeKind.Modified),
            (FrozenStatePathValue, RawChangeKind.Modified)).Diagnostics);

        Assert.Equal(AdmissionEffect.Observe, diagnostic.AdmissionEffect);
        Assert.Equal(
            $"FROZEN_PIN_CHANGE selector={FrozenPath} old={oldPin.Value} new={newPin.Value}",
            diagnostic.Message);
    }

    [Fact]
    public void Sl008EmitsOnePinChangeObservationPerSelectorInOrdinalOrder()
    {
        var fixture = new RuleFixture();
        var modules = new[] { RuleFixture.ValuesBindingPath, FrozenPath };
        var changes = new List<(string Path, RawChangeKind Kind)>();
        var expected = new List<string>();
        foreach (var module in modules)
        {
            var oldPin = ModuleStatementId(fixture, module);
            AddState(fixture, module, oldPin, includeInBaseline: true);
            ChangeStatement(fixture, module, "String");
            var newPin = ModuleStatementId(fixture, module);
            AddState(fixture, module, newPin);
            var statePath = FrozenStatePath.FromModulePath(RepoPath.CreateKnown(module)).Value;
            changes.Add((statePath, RawChangeKind.Modified));
            expected.Add(
                $"FROZEN_PIN_CHANGE selector={module} old={oldPin.Value} new={newPin.Value}");
        }

        var diagnostics = Evaluate(fixture, changes.ToArray()).Diagnostics;

        Assert.All(diagnostics, diagnostic =>
            Assert.Equal(AdmissionEffect.Observe, diagnostic.AdmissionEffect));
        Assert.Equal(expected.Order(StringComparer.Ordinal), diagnostics.Select(static item => item.Message));
    }

    [Fact]
    public void Sl008RechecksFrozenReverseImportDependentsOfAChangedModule()
    {
        var fixture = new RuleFixture();
        var downstream = RuleFixture.ValuesBindingPath;
        var stored = ModuleStatementId(fixture, downstream);
        AddState(fixture, downstream, stored, includeInBaseline: true);
        fixture.Reports[downstream] = new LeanFileReport(
            ["D5.S0.Carrier.Ring"],
            [new LeanDeclaration(
                "fixtureValue",
                "def",
                "Nat",
                ImmutableArray.Create("Classical.choice", "Quot.sound", "propext"))]);
        var actual = ModuleStatementId(fixture, downstream);
        Assert.NotEqual(stored, actual);

        var diagnostic = Assert.Single(
            Evaluate(fixture, (FrozenPath, RawChangeKind.Modified)).Diagnostics);

        Assert.Contains($"selector {downstream}", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains($"stored={stored.Value}", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains($"actual={actual.Value}", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008RechecksFrozenDependentThroughBaselineOnlyImportEdge()
    {
        var fixture = new RuleFixture();
        var dependent = RuleFixture.ValuesBindingPath;
        var actual = ModuleStatementId(fixture, dependent);
        var stored = StatementId.Create("sha256:" + new string('f', 64));
        Assert.NotEqual(stored, actual);
        AddState(fixture, dependent, stored, includeInBaseline: true);
        var baselineSource = fixture.Baseline[dependent].Replace(
            "def fixtureValue",
            "\nimport D5.S0.Carrier.Ring\n\ndef fixtureValue",
            StringComparison.Ordinal);
        fixture.Baseline[dependent] = baselineSource;
        fixture.ForkPoint[dependent] = baselineSource;
        fixture.BaselineReports[dependent] = fixture.BaselineReports[dependent] with
        {
            Imports = ["D5.S0.Carrier.Ring"],
        };
        fixture.Files[FrozenPath] = fixture.Files[FrozenPath].Replace(
            "def goldenRing : Nat := 0",
            "def goldenRing : Int := 0",
            StringComparison.Ordinal);
        ChangeStatement(fixture, FrozenPath, "Int");

        var diagnostic = Assert.Single(
            Evaluate(fixture, (FrozenPath, RawChangeKind.Modified)).Diagnostics);

        Assert.Contains($"selector {dependent}", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains($"stored={stored.Value}", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains($"actual={actual.Value}", diagnostic.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("tools/lean-inspector/inspect.sh")]
    [InlineData("tools/lean-inspector/materials.py")]
    [InlineData("tools/scripts/report/lean-report-input.sh")]
    [InlineData("lean-toolchain")]
    [InlineData("lakefile.toml")]
    [InlineData("lake-manifest.json")]
    [InlineData("tools/StrataLint.Engine/Rules/RepositoryRules.FrozenState.cs")]
    public void Sl008RechecksEveryCurrentStateForEachReportInputCategory(string changedPath)
    {
        var fixture = new RuleFixture();
        var modules = new[] { FrozenPath, RuleFixture.ValuesBindingPath };
        foreach (var module in modules)
        {
            AddState(
                fixture,
                module,
                StatementId.Create("sha256:" + new string(module == FrozenPath ? 'a' : 'b', 64)));
        }

        var diagnostics = Evaluate(fixture, (changedPath, RawChangeKind.Modified)).Diagnostics;

        Assert.Equal(modules.Length, diagnostics.Length);
        Assert.Equal(
            modules.Order(StringComparer.Ordinal),
            diagnostics.Select(static diagnostic => diagnostic.Message.Split(' ')[1]));
    }

    [Fact]
    public void Sl008DoesNotRecheckCurrentStatesForAnUnrelatedPath()
    {
        var fixture = new RuleFixture();
        foreach (var module in new[] { FrozenPath, RuleFixture.ValuesBindingPath })
        {
            AddState(
                fixture,
                module,
                StatementId.Create("sha256:" + new string('f', 64)));
        }

        var evaluation = Evaluate(fixture, ("README.md", RawChangeKind.Modified));

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl008DoesNotWakeUnrelatedStateForManagedLeanChange()
    {
        var fixture = new RuleFixture();
        AddState(
            fixture,
            RuleFixture.ValuesBindingPath,
            StatementId.Create("sha256:" + new string('f', 64)));

        var evaluation = Evaluate(fixture, (FrozenPath, RawChangeKind.Modified));

        Assert.Empty(evaluation.Diagnostics);
    }

    private static RuleFixture FrozenFixture(out string eventPath)
    {
        var fixture = new RuleFixture();
        eventPath = AddFreeze(fixture, FrozenPath);
        return fixture;
    }

    private static string AddFreeze(
        RuleFixture fixture,
        string descriptorSelector,
        StatementId? statementId = null)
    {
        var path = RepoPath.CreateKnown(descriptorSelector);
        var declarations = CanonicalStatementWriter.DeclarationStatementIds(
            path,
            fixture.Reports[descriptorSelector]);
        var material = new FrozenNodeMaterial(
            path,
            declarations,
            statementId ?? FrozenContentAddress.ComputeModuleStatementId(
                path,
                fixture.Reports[descriptorSelector]),
            FrozenNodeId.Create("sha256:" + new string('0', 64)),
            [],
            []);
        var payload = FrozenLedgerCanonicalWriter.FreezeElement(
            FrozenLedgerCanonicalWriter.FreezePayload(material));
        var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent("Freeze", payload);
        var eventPath = FrozenLedgerChangeClassifier.AcceptedPath(encoded.Hash);
        fixture.Files[eventPath] = Encoding.UTF8.GetString(encoded.Bytes.AsSpan());
        return eventPath;
    }

    private static StatementId ModuleStatementId(RuleFixture fixture, string modulePath)
    {
        var path = RepoPath.CreateKnown(modulePath);
        return FrozenContentAddress.ComputeModuleStatementId(path, fixture.Reports[modulePath]);
    }

    private static void ChangeStatement(
        RuleFixture fixture,
        string modulePath,
        string statementMaterial)
    {
        var report = fixture.Reports[modulePath];
        fixture.Reports[modulePath] = report with
        {
            Declarations = report.Declarations
                .Select(declaration => declaration with { TypeRepresentation = statementMaterial })
                .ToImmutableArray(),
        };
    }

    private static void AddState(
        RuleFixture fixture,
        string modulePath,
        StatementId statementId,
        bool includeInBaseline = false)
    {
        var statePath = FrozenStatePath.FromModulePath(RepoPath.CreateKnown(modulePath)).Value;
        fixture.Files[statePath] = StateText(statementId);
        if (includeInBaseline)
        {
            fixture.Baseline[statePath] = fixture.Files[statePath];
            fixture.ForkPoint[statePath] = fixture.Files[statePath];
        }
    }

    private static string StateText(StatementId statementId) =>
        $"{{\"statement_id\":\"{statementId.Value}\"}}\n";

    private static SingleRuleEvaluation Evaluate(
        RuleFixture fixture,
        params (string Path, RawChangeKind Kind)[] changes) =>
        RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(8),
            fixture.Build(RawChangeSet.CreateWithKinds(changes)));

}
