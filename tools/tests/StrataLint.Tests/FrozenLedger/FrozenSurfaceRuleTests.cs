using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class FrozenSurfaceRuleTests
{
    private const string FrozenPath = RuleFixture.RingPath;
    private const string OtherPath = RuleFixture.BlueprintPath;
    // Derived with POSIX printf and shasum -a 256 over the documented statement
    // domain prefix and canonical declaration/module JSON, outside production code.
    private const string ExpectedFrozenModuleStatementPin =
        "sha256:3d2b9bf06c5fb9076c8206428611c597cc723e59b64f5415e7dae6049ee954e2";
    private const string ExpectedChangedFrozenModuleStatementPin =
        "sha256:410bb522f539e28e4d11d468ba910476da9a0462246fc575d54526b3c57d0a2e";
    private static readonly string FrozenStatePathValue =
        FrozenStatePath.FromModulePath(RepoPath.CreateKnown(FrozenPath)).Value;

    public static TheoryData<string> LeanReportProducerInputCategories => new()
    {
        "tools/StrataLint.Cli/Program.cs",
        "tools/StrataLint.Engine/Rules/RepositoryRules.FrozenState.cs",
        "tools/StrataLint.Scribe/ScribeEmitter.cs",
        "tools/Trureturing.Truth/Truth.cs",
        "tools/Trureturing.Truth/Trureturing.Truth.csproj",
        "tools/lean-inspector/Inspector.lean",
        "tools/scripts/report/lean-report-input.sh",
        "tools/scripts/workflow/ci-engineering.sh",
        "tools/scripts/worktree/lean-cache-ensure.sh",
        "tools/scripts/lib/resource-observation-lib.sh",
        "tools/scripts/lean-report-pair.sh",
        ".github/workflows/ci.yml",
        "Directory.Build.props",
        "Directory.Build.targets",
        "Directory.Packages.props",
        "global.json",
        "lean-toolchain",
        "lakefile.toml",
        "lakefile.lean",
        "lake-manifest.json",
    };

    public static TheoryData<string> IndependentlyWakingLeanReportProducerInputs => new()
    {
        "tools/StrataLint.Cli/Program.cs",
        "tools/StrataLint.Scribe/ScribeEmitter.cs",
        "tools/Trureturing.Truth/Truth.cs",
        "tools/Trureturing.Truth/Trureturing.Truth.csproj",
        "tools/lean-inspector/Inspector.lean",
        "tools/scripts/report/lean-report-input.sh",
        "tools/scripts/workflow/ci-engineering.sh",
        "tools/scripts/worktree/lean-cache-ensure.sh",
        "tools/scripts/lib/resource-observation-lib.sh",
        "tools/scripts/lean-report-pair.sh",
        ".github/workflows/ci.yml",
        "lean-toolchain",
        "lakefile.toml",
        "lakefile.lean",
        "lake-manifest.json",
    };

    public static TheoryData<string> CatalogProducerWakeupInputs => new()
    {
        "lean-toolchain",
        ".github/workflows/ci.yml",
        "tools/StrataLint.Cli/Program.cs",
    };

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
        else
        {
            AddState(fixture, FrozenPath, ModuleStatementId(fixture, FrozenPath));
        }

        var evaluation = Evaluate(fixture, (eventPath, kind));

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl008AllowsAddedAcceptedEventFragment()
    {
        var fixture = FrozenFixture(out var eventPath);
        AddState(fixture, FrozenPath, ModuleStatementId(fixture, FrozenPath));

        var evaluation = Evaluate(fixture, (eventPath, RawChangeKind.Added));

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl008IgnoresModifiedNonFrozenModule()
    {
        var fixture = FrozenFixture(out _);
        AddState(fixture, FrozenPath, ModuleStatementId(fixture, FrozenPath));

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
    public void Sl008C6aBlocksAddedFreezeWithoutFrozenStatePin()
    {
        var fixture = new RuleFixture();
        var eventPath = AddFreeze(fixture, FrozenPath);

        var diagnostic = Assert.Single(
            Evaluate(fixture, (eventPath, RawChangeKind.Added)).Diagnostics);

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal(eventPath, diagnostic.Path);
        Assert.Contains(FrozenPath, diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains(FrozenStatePathValue, diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("run ledger-align --from-accepted", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008C6AllowsAddedFreezeWithMatchingFrozenStatePin()
    {
        var fixture = new RuleFixture();
        var pin = ModuleStatementId(fixture, FrozenPath);
        var eventPath = AddFreeze(fixture, FrozenPath, pin);
        AddState(fixture, FrozenPath, pin);

        var evaluation = Evaluate(fixture, (eventPath, RawChangeKind.Added));

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl008C6bBlocksAddedFreezeWithMismatchedFrozenStatePin()
    {
        var fixture = new RuleFixture();
        var eventPin = ModuleStatementId(fixture, FrozenPath);
        var statePin = StatementId.Create("sha256:" + new string('e', 64));
        Assert.NotEqual(eventPin, statePin);
        var eventPath = AddFreeze(fixture, FrozenPath, eventPin);
        AddState(fixture, FrozenPath, statePin);

        var diagnostic = Assert.Single(
            Evaluate(fixture, (eventPath, RawChangeKind.Added)).Diagnostics);

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal(eventPath, diagnostic.Path);
        Assert.Contains($"selector={FrozenPath}", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains($"event pin={eventPin.Value}", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains($"state pin={statePin.Value}", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008C6IgnoresAddedRevokeWithoutFrozenStatePin()
    {
        var fixture = new RuleFixture();
        var eventPath = AddNonFreezeAcceptedEvent(fixture, "Revoke", 'c');

        var evaluation = Evaluate(fixture, (eventPath, RawChangeKind.Added));

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl008C6IgnoresUnchangedAcceptedFreezeWithoutFrozenStatePin()
    {
        var fixture = new RuleFixture();
        var eventPath = AddFreeze(fixture, FrozenPath);
        fixture.Baseline[eventPath] = fixture.Files[eventPath];
        fixture.ForkPoint[eventPath] = fixture.Files[eventPath];

        var evaluation = Evaluate(fixture);

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl008C6FailsClosedForMalformedAddedAcceptedEvent()
    {
        var fixture = new RuleFixture();
        var eventPath = FrozenLedgerChangeClassifier.AcceptedPath(
            "sha256:" + new string('d', 64));
        fixture.Files[eventPath] = "{}\n";

        var diagnostic = Assert.Single(
            Evaluate(fixture, (eventPath, RawChangeKind.Added)).Diagnostics);

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal(eventPath, diagnostic.Path);
        Assert.Contains(
            "content-addressed event envelope has unknown, missing, or duplicate fields.",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008CatalogExecutesC6ForAddedAcceptedFreezeWithoutFrozenStatePin()
    {
        var fixture = new RuleFixture();
        var eventPath = AddFreeze(fixture, FrozenPath);

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(
                RawChangeSet.CreateWithKinds([(eventPath, RawChangeKind.Added)])))).Capability;

        var diagnostic = Assert.Single(completed.Diagnostics, static diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(8));
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal(eventPath, diagnostic.Path);
        Assert.Contains(FrozenPath, diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains(FrozenStatePathValue, diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains(RuleId.CreateKnown(8), completed.ExecutedRules);
    }

    [Fact]
    public void Sl008AllowsHeaderOrCommentChangesWhenTheModulePinIsUnchanged()
    {
        var fixture = new RuleFixture();
        var pin = StatementId.Create(ExpectedFrozenModuleStatementPin);
        AddState(fixture, FrozenPath, pin, includeInBaseline: true);
        _ = AddFreeze(fixture, FrozenPath, pin);
        var baselineSource = fixture.Baseline[FrozenPath];
        fixture.Files[FrozenPath] = fixture.Files[FrozenPath].Replace(
            "anchors: []",
            "anchors: [mathlib/module/Nat]",
            StringComparison.Ordinal);
        var currentSource = fixture.Files[FrozenPath];
        var (baselineHeader, baselineStatements) = SplitSixLineHeader(baselineSource);
        var (currentHeader, currentStatements) = SplitSixLineHeader(currentSource);
        var baselineAnchors = HeaderField(baselineHeader, "anchors");
        var currentAnchors = HeaderField(currentHeader, "anchors");

        Assert.NotEqual(baselineSource, currentSource);
        Assert.Equal("anchors: []", baselineAnchors);
        Assert.Equal("anchors: [mathlib/module/Nat]", currentAnchors);
        Assert.NotEqual(baselineAnchors, currentAnchors);
        Assert.Equal(
            Encoding.UTF8.GetBytes(baselineStatements),
            Encoding.UTF8.GetBytes(currentStatements));
        var freshPin = ModuleStatementId(fixture, FrozenPath);
        Assert.Equal(pin, freshPin);

        var evaluation = Evaluate(fixture, (FrozenPath, ChangeKindBetween(fixture, FrozenPath)));

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
        var oldPin = StatementId.Create(ExpectedFrozenModuleStatementPin);
        Assert.Equal(oldPin, ModuleStatementId(fixture, FrozenPath));
        AddState(fixture, FrozenPath, oldPin, includeInBaseline: true);
        fixture.Files[FrozenPath] = fixture.Files[FrozenPath].Replace(
            "def goldenRing : Nat := 0",
            "def goldenRing : Int := 0",
            StringComparison.Ordinal);
        ChangeStatement(fixture, FrozenPath, "Int");
        var newPin = StatementId.Create(ExpectedChangedFrozenModuleStatementPin);
        Assert.Equal(newPin, ModuleStatementId(fixture, FrozenPath));
        AddState(fixture, FrozenPath, newPin);

        var diagnostic = Assert.Single(Evaluate(
            fixture,
            (FrozenPath, RawChangeKind.Modified),
            (FrozenStatePathValue, RawChangeKind.Modified)).Diagnostics);

        Assert.Equal(
            $"FROZEN_PIN_CHANGE selector={FrozenPath} old={oldPin.Value} new={newPin.Value}",
            diagnostic.Message);
        Assert.Equal(AdmissionEffect.Observe, diagnostic.AdmissionEffect);
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
            "\nimport D5.S0.Carrier.Ring\nimport Mathlib.Data.Nat.Basic\n\ndef fixtureValue",
            StringComparison.Ordinal);
        fixture.Baseline[dependent] = baselineSource;
        fixture.ForkPoint[dependent] = baselineSource;
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

    [Fact]
    public void SourceParsedImportsMatchReportAdjacencyForTheCurrentSnapshot()
    {
        var fixture = new RuleFixture();
        var dependent = RuleFixture.ValuesBindingPath;
        fixture.Files[dependent] = fixture.Files[dependent].Replace(
            "def fixtureValue",
            "\nimport D5.S0.Carrier.Ring\n\ndef fixtureValue",
            StringComparison.Ordinal);
        fixture.Reports[dependent] = fixture.Reports[dependent] with
        {
            Imports = ["D5.S0.Carrier.Ring"],
        };
        var context = fixture.Build(RawChangeSet.Create([]));

        var fromSources = LeanImportAdjacency.BuildFromSources(context.Current)
            .OrderBy(static item => item.Key.Value, StringComparer.Ordinal)
            .Select(static item => (
                Module: item.Key.Value,
                Dependencies: string.Join(',', item.Value.Select(static path => path.Value))))
            .ToArray();
        var fromReport = LeanImportAdjacency.Build(context.Current, context.Lean)
            .OrderBy(static item => item.Key.Value, StringComparer.Ordinal)
            .Select(static item => (
                Module: item.Key.Value,
                Dependencies: string.Join(',', item.Value.Select(static path => path.Value))))
            .ToArray();

        Assert.Equal(fromReport, fromSources);
    }

    [Theory]
    [MemberData(nameof(LeanReportProducerInputCategories))]
    public void LeanReportProducerInputPredicateCoversEachCanonicalCategory(string path)
    {
        Assert.True(RepositoryRules.IsLeanReportProducerInput(path));
    }

    [Theory]
    [InlineData("D5/X.lean")]
    [InlineData("Blueprint/D5/X.scribe.cs")]
    [InlineData("Golden/Frozen/state/X.lean.json")]
    [InlineData("Meta/Digestion/atoms/sha256/abc")]
    [InlineData("docs/develop/theory/X.md")]
    [InlineData("tools/tests/StrataLint.Tests/X.cs")]
    public void LeanReportProducerInputPredicateExcludesContentProjectionAndTestPaths(string path)
    {
        Assert.False(RepositoryRules.IsLeanReportProducerInput(path));
    }

    [Theory]
    [MemberData(nameof(IndependentlyWakingLeanReportProducerInputs))]
    public void Sl008RechecksEveryCurrentStateForEachIndependentProducerInput(string changedPath)
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

    [Theory]
    [MemberData(nameof(CatalogProducerWakeupInputs))]
    public void Sl008CatalogExecutionBlocksStalePinWhenProducerInputChanges(string changedPath)
    {
        var fixture = new RuleFixture();
        AddState(
            fixture,
            FrozenPath,
            StatementId.Create("sha256:" + new string('f', 64)),
            includeInBaseline: true);

        var completed = ExecuteCatalogWithOnlyModifiedPath(fixture, changedPath);

        var diagnostic = Assert.Single(completed.Diagnostics.Where(static diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(8)));
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Contains("pin mismatch", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains(RuleId.CreateKnown(8), completed.ExecutedRules);
    }

    [Fact]
    public void Sl008CatalogExecutionDoesNotReportStalePinForUnrelatedDocsChange()
    {
        var fixture = new RuleFixture();
        AddState(
            fixture,
            FrozenPath,
            StatementId.Create("sha256:" + new string('f', 64)),
            includeInBaseline: true);

        var completed = ExecuteCatalogWithOnlyModifiedPath(fixture, "docs/x.md");

        Assert.DoesNotContain(completed.Diagnostics, static diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(8));
        Assert.Contains(RuleId.CreateKnown(8), completed.SkippedRules);
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

    private static string AddNonFreezeAcceptedEvent(
        RuleFixture fixture,
        string eventType,
        char hashDigit)
    {
        var eventHash = "sha256:" + new string(hashDigit, 64);
        var eventPath = FrozenLedgerChangeClassifier.AcceptedPath(eventHash);
        fixture.Files[eventPath] =
            $"{{\"event_hash\":\"{eventHash}\",\"event_type\":\"{eventType}\","
            + "\"payload\":{},\"schema_version\":5}\n";
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

    private static (string Header, string Statements) SplitSixLineHeader(string source)
    {
        var statementStart = 0;
        for (var line = 0; line < 6; line++)
        {
            var lineEnd = source.IndexOf('\n', statementStart);
            Assert.True(lineEnd >= 0, "fixture source must contain a complete six-line header");
            statementStart = lineEnd + 1;
        }

        return (source[..statementStart], source[statementStart..]);
    }

    private static string HeaderField(string header, string fieldName) =>
        Assert.Single(
            header.Split('\n', StringSplitOptions.RemoveEmptyEntries)
                .Select(static line => line.Trim()),
            line => line.StartsWith($"{fieldName}:", StringComparison.Ordinal));

    private static RawChangeKind ChangeKindBetween(RuleFixture fixture, string path)
    {
        var baselineExists = fixture.Baseline.TryGetValue(path, out var baseline);
        var currentExists = fixture.Files.TryGetValue(path, out var current);
        return (baselineExists, currentExists) switch
        {
            (false, true) => RawChangeKind.Added,
            (true, false) => RawChangeKind.Deleted,
            (true, true) when !string.Equals(baseline, current, StringComparison.Ordinal) =>
                RawChangeKind.Modified,
            _ => throw new InvalidOperationException($"{path} is unchanged between fixture snapshots"),
        };
    }

    private static SingleRuleEvaluation Evaluate(
        RuleFixture fixture,
        params (string Path, RawChangeKind Kind)[] changes) =>
        RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(8),
            fixture.Build(RawChangeSet.CreateWithKinds(changes)));

    private static CompletedRuleSet ExecuteCatalogWithOnlyModifiedPath(
        RuleFixture fixture,
        string changedPath)
    {
        fixture.Baseline[changedPath] = "baseline\n";
        fixture.ForkPoint[changedPath] = "baseline\n";
        fixture.Files[changedPath] = "candidate\n";
        return Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(
                RawChangeSet.CreateWithKinds([(changedPath, RawChangeKind.Modified)])))).Capability;
    }

}
