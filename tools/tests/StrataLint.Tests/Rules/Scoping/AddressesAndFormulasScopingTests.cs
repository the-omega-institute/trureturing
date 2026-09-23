using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class AddressesAndFormulasScopingTests
{
    private const string FormulaPath = "Evidence/D5/S0/Carrier/Formula.check.json";
    private const string UnrelatedPath = "notes/unrelated.txt";

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void FormulaBodiesFollowRegisteredMaterialsWithoutChangingGovernanceRejection(bool includeExperiment)
    {
        const string experiment = "docs/reports/example/results.json";
        var fixture = new RuleFixture();
        RegisterFormulaMaterials(fixture, includeExperiment ? ["Evidence/**/*.json", experiment] : ["Evidence/**/*.json"]);
        SetOldSnapshotFile(fixture, experiment,
            "{\"kind\":\"inline\",\"value\":{\"formula\":\"T >= sum of source bounds\"}}\n");
        SetOldSnapshotFile(fixture, FormulaPath, "{\"formula\":\"sqrt@5\",\"refs\":{}}\n");
        SetUnrelatedDelta(fixture);

        var result = Execute(fixture, UnrelatedPath);

        Assert.Contains(result.Diagnostics, diagnostic => diagnostic.RuleId == RuleId.CreateKnown(15)
            && diagnostic.Path == FormulaPath && diagnostic.Message.Contains("illegal formula character", StringComparison.Ordinal));
        Assert.Equal(includeExperiment, result.Diagnostics.Any(diagnostic => diagnostic.RuleId == RuleId.CreateKnown(15)
            && diagnostic.Path == experiment && diagnostic.Message == "formula and refs must be string/object"));
    }

    [Fact]
    public void FormulaMaterialExclusionsDoNotSuppressRepositoryPathPolicy()
    {
        const string invalidPath = "Evidence/D5/S0/Carrier/Probe.unknown.json";
        var fixture = new RuleFixture();
        RegisterFormulaMaterials(fixture, ["Evidence/**/*.json"], [FormulaPath, invalidPath]);
        SetOldSnapshotFile(fixture, FormulaPath, "{\"formula\":\"sqrt@5\",\"refs\":{}}\n");
        SetOldSnapshotFile(fixture, invalidPath, "{\"formula\":\"sqrt@5\",\"refs\":{}}\n");

        var result = Execute(fixture, UnrelatedPath);

        Assert.DoesNotContain(result.Diagnostics, diagnostic => diagnostic.Path == FormulaPath);
        Assert.Contains(result.Diagnostics, diagnostic => diagnostic.Path == invalidPath
            && diagnostic.Message.Contains("path is outside the registry artifact kind/selector whitelist", StringComparison.Ordinal));
    }

    [Fact]
    public void RepositoryRegistrationKeepsExperimentJsonOutsideFormulaInputs()
    {
        const string experiment = "docs/reports/erdos7-odd-covering/certificates/source_norms/source-budgets/"
            + "source_own_test_consumer.parts/content/008-reweighted_full_haar_chain.json";
        var fixture = new RuleFixture();
        var manifest = TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create("Meta/ci-checks.json"));
        fixture.Files["Meta/ci-checks.json"] = manifest;
        using var document = System.Text.Json.JsonDocument.Parse(manifest);
        var declaration = document.RootElement.GetProperty("checks").EnumerateArray()
            .Single(check => check.GetProperty("id").GetString() == "SL-015");
        foreach (var item in declaration.GetProperty("materials").EnumerateArray())
        {
            var path = item.GetString()!;
            if (!path.Contains('*')) fixture.Files.TryAdd(path, path.EndsWith(".json", StringComparison.Ordinal) ? "{}\n" : "\n");
        }
        SetOldSnapshotFile(fixture, experiment, "{\"kind\":\"inline\",\"value\":{\"formula\":\"T >= source bounds\"}}\n");
        SetOldSnapshotFile(fixture, FormulaPath, "{\"formula\":\"sqrt@5\",\"refs\":{}}\n");

        var data = fixture.BuildForRuleCompatibility();
        var result = RepositoryRules.FormulaValidation(CurrentRuleContext.Create(data.Current, data.Policy, data.Lean));

        Assert.Single(result);
        Assert.Equal(FormulaPath, result[0].Path);
        Assert.Contains("illegal formula character", result[0].Message, StringComparison.Ordinal);
    }

    [Fact]
    public void EmptyRegisteredFormulaInputsDoNotFallBackToAllJson()
    {
        var fixture = new RuleFixture();
        RegisterFormulaMaterials(fixture, []);
        SetOldSnapshotFile(fixture, FormulaPath, "{\"formula\":\"sqrt@5\",\"refs\":{}}\n");

        var result = Execute(fixture, UnrelatedPath);

        Assert.DoesNotContain(result.Diagnostics, diagnostic => diagnostic.RuleId == RuleId.CreateKnown(15));
    }

    [Theory]
    [InlineData(null)]
    [InlineData("{")]
    [InlineData("{\"schema\":\"ci-check-input-registration-v2\",\"checks\":[]}")]
    [InlineData("{\"schema\":\"wrong\",\"checks\":[{\"id\":\"SL-015\",\"materials\":[],\"material_excludes\":[]}]}")]
    [InlineData("{\"schema\":\"ci-check-input-registration-v2\",\"checks\":[{\"id\":\"SL-015\",\"materials\":[\"../**\"],\"material_excludes\":[]}]}")]
    [InlineData("{\"schema\":\"ci-check-input-registration-v2\",\"checks\":[{\"id\":\"SL-015\",\"materials\":[],\"material_excludes\":[]},{\"id\":\"SL-015\",\"materials\":[],\"material_excludes\":[]}]}")]
    [InlineData("{\"schema\":\"ci-check-input-registration-v2\",\"checks\":[{\"id\":\"SL-015\",\"materials\":null,\"material_excludes\":[]}]}")]
    [InlineData("{\"schema\":\"ci-check-input-registration-v2\",\"checks\":[{\"id\":\"SL-015\",\"materials\":[],\"materials\":[\"**\"],\"material_excludes\":[]}]}")]
    [InlineData("{\"schema\":\"ci-check-input-registration-v2\",\"checks\":[{\"id\":\"SL-015\",\"materials\":[\"**\",\"**\"],\"material_excludes\":[]}]}")]
    [InlineData("{\"schema\":\"ci-check-input-registration-v2\",\"checks\":[{\"id\":\"SL-015\",\"materials\":[\"Meta/registry.yaml\"],\"material_excludes\":[\"Meta/**\"]}]}")]
    [InlineData("{\"schema\":\"ci-check-input-registration-v2\",\"checks\":[{\"id\":\"SL-015\",\"materials\":[\"Evidence/absent.json\"],\"material_excludes\":[]}]}")]
    public void MissingOrInvalidFormulaRegistrationFailsExplicitly(string? manifest)
    {
        var fixture = new RuleFixture();
        if (manifest is null) fixture.Files.Remove("Meta/ci-checks.json");
        else fixture.Files["Meta/ci-checks.json"] = manifest;

        var result = Execute(fixture, UnrelatedPath);

        Assert.Contains(result.Diagnostics, diagnostic => diagnostic.RuleId == RuleId.CreateKnown(15)
            && diagnostic.Path == "Meta/ci-checks.json"
            && diagnostic.Message.Contains("registration", StringComparison.Ordinal));
    }

    private static void RegisterFormulaMaterials(RuleFixture fixture, string[] materials, string[]? excludes = null) =>
        fixture.Files["Meta/ci-checks.json"] = System.Text.Json.JsonSerializer.Serialize(new
        {
            schema = "ci-check-input-registration-v2",
            checks = new[] { new { id = "SL-015", materials, material_excludes = excludes ?? [] } },
        });

    [Fact]
    [BaseFactScopeProbe(
        15,
        typeof(RepositoryRules),
        nameof(RepositoryRules.FormulaValidation))]
    public void Sl015FormulaValidationChecksCurrentMalformedFormulaOutsideCandidateDelta()
    {
        var fixture = new RuleFixture();
        SetOldSnapshotFile(fixture, FormulaPath, "{\"formula\":\"sqrt@5\",\"refs\":{}}\n");
        SetUnrelatedDelta(fixture);

        var completed = Execute(fixture, UnrelatedPath);

        Assert.Contains(RuleId.CreateKnown(15), completed.ExecutedRules);
        Assert.Contains(completed.Diagnostics, diagnostic => diagnostic.Path == FormulaPath);

        var changed = new RuleFixture();
        changed.Baseline[FormulaPath] = "{\"formula\":\"5\",\"refs\":{}}\n";
        changed.Files[FormulaPath] = "{\"formula\":\"sqrt@5\",\"refs\":{}}\n";
        Assert.Contains(Execute(changed, FormulaPath).Diagnostics, diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(15)
            && diagnostic.Path == FormulaPath
            && diagnostic.Message.Contains("illegal formula character", StringComparison.Ordinal));

        var implementation = new RuleFixture();
        SetOldSnapshotFile(implementation, FormulaPath, "{\"formula\":\"sqrt@5\",\"refs\":{}}\n");
        Assert.Contains(
            Execute(implementation, "tools/StrataLint.Engine/Rules/RepositoryRules.Formulas.cs").Diagnostics,
            diagnostic => diagnostic.RuleId == RuleId.CreateKnown(15)
                && diagnostic.Path == FormulaPath
                && diagnostic.Message.Contains("illegal formula character", StringComparison.Ordinal));
    }

    [Fact]
    public void Sl015StillValidatesMalformedFormulaInsideCandidateDelta()
    {
        var fixture = new RuleFixture();
        fixture.Baseline[FormulaPath] = "{\"formula\":\"5\",\"refs\":{}}\n";
        fixture.Files[FormulaPath] = "{\"formula\":\"sqrt@5\",\"refs\":{}}\n";

        var completed = Execute(fixture, FormulaPath);

        Assert.Contains(completed.Diagnostics, diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(15)
            && diagnostic.Path == FormulaPath
            && diagnostic.Message.Contains("illegal formula character", StringComparison.Ordinal));
    }

    [Fact]
    public void Sl015ChecksCurrentDuplicateGidForUnrelatedCandidateDelta()
    {
        var fixture = new RuleFixture();
        SetOldSnapshotFile(fixture, RuleFixture.BlueprintPath, fixture.Files[RuleFixture.RingPath]);
        SetUnrelatedDelta(fixture);

        var completed = Execute(fixture, UnrelatedPath);

        Assert.Contains(completed.Diagnostics, diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(15)
            && diagnostic.Message.Contains("duplicate GID", StringComparison.Ordinal));
    }

    [Fact]
    public void Sl015ChecksCurrentEvidenceSelectorCollisionForUnrelatedCandidateDelta()
    {
        const string jsonPath = "Evidence/D5/S0/Carrier/Probe.result.json";
        const string yamlPath = "Evidence/D5/S0/Carrier/Probe.result.yaml";
        var fixture = new RuleFixture();
        SetOldSnapshotFile(fixture, jsonPath, "{}\n");
        SetOldSnapshotFile(fixture, yamlPath, "value: fixture\n");
        SetUnrelatedDelta(fixture);

        var completed = Execute(fixture, UnrelatedPath);

        Assert.Contains(completed.Diagnostics, diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(15)
            && diagnostic.Message.Contains(
                "evidence selector has multiple artifact kinds",
                StringComparison.Ordinal));
    }

    private static CompletedRuleSet Execute(RuleFixture fixture, string changedPath) =>
        Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(RawChangeSet.Create([changedPath])))).Capability;

    private static void SetOldSnapshotFile(RuleFixture fixture, string path, string text)
    {
        fixture.Files[path] = text;
        fixture.Baseline[path] = text;
    }

    private static void SetUnrelatedDelta(RuleFixture fixture)
    {
        fixture.Baseline[UnrelatedPath] = "old\n";
        fixture.Files[UnrelatedPath] = "candidate\n";
    }
}
