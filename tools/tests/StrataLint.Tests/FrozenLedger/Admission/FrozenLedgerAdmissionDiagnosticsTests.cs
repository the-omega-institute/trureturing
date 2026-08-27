using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class FrozenLedgerAdmissionDiagnosticsTests
{
    private const string ModulePath = "D5/S0/Carrier/A.lean";
    private const string AlternateModulePath = "D5/S0/Carrier/Actual.lean";

    [Fact]
    public void Sl008AdmissionAllowsRecordedContentAddressesToDiffer()
    {
        var scenario = CreateScenario("WitnessId", "FrozenNodeId");
        var recordedDependency = DependencyMaterial("RecordedDependency", '4');
        var currentDependency = DependencyMaterial("RecordedDependency", '5');
        scenario = scenario with
        {
            ActualMaterial = scenario.ActualMaterial with
            {
                PrerequisiteFrozenNodeIds = [recordedDependency.FrozenNodeId],
            },
            ExpectedMaterial = scenario.ExpectedMaterial with
            {
                PrerequisiteFrozenNodeIds = [currentDependency.FrozenNodeId],
            },
            ActualDependencies = [recordedDependency],
            ExpectedDependencies = [currentDependency],
        };
        scenario = scenario with { Payload = PayloadFrom(scenario.ActualMaterial) };

        Assert.Null(Evaluate(scenario));
    }

    [Fact]
    public void Sl008AdmissionRejectsPrerequisitePathDrift()
    {
        var scenario = CreateScenario("match");
        var recordedDependency = DependencyMaterial("RecordedDependency", '4');
        var currentDependency = DependencyMaterial("CurrentDependency", '5');
        scenario = scenario with
        {
            ActualMaterial = scenario.ActualMaterial with
            {
                PrerequisiteFrozenNodeIds = [recordedDependency.FrozenNodeId],
            },
            ExpectedMaterial = scenario.ExpectedMaterial with
            {
                PrerequisiteFrozenNodeIds = [currentDependency.FrozenNodeId],
            },
            ActualDependencies = [recordedDependency],
            ExpectedDependencies = [currentDependency],
        };
        scenario = scenario with { Payload = PayloadFrom(scenario.ActualMaterial) };

        var failure = Assert.IsType<FrozenLedgerAdmissionFailure>(Evaluate(scenario));

        Assert.Contains("PrerequisitePaths", failure.Message, StringComparison.Ordinal);
        Assert.Contains("RecordedDependency.lean", failure.Message, StringComparison.Ordinal);
        Assert.Contains("CurrentDependency.lean", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008AdmissionAllowsUnresolvableRecordedPrerequisiteIdentity()
    {
        var scenario = CreateScenario("match");
        scenario = scenario with
        {
            ActualMaterial = scenario.ActualMaterial with
            {
                PrerequisiteFrozenNodeIds = [FrozenNodeId.Create(Sha256('4'))],
            },
        };
        scenario = scenario with { Payload = PayloadFrom(scenario.ActualMaterial) };

        Assert.Null(Evaluate(scenario));
    }

    [Fact]
    public void Sl008AdmissionNormalizesAxiomClosureAsASet()
    {
        var scenario = CreateScenario("match");
        scenario = scenario with
        {
            ExpectedMaterial = scenario.ExpectedMaterial with
            {
                AxiomClosure = ["propext", "Classical.choice", "propext"],
            },
        };

        Assert.Null(Evaluate(scenario));
    }

    [Fact]
    public void Sl008AdmissionAllowsHistoricalEventWithoutAxiomClosure()
    {
        var scenario = CreateScenario("match");
        scenario = scenario with
        {
            Payload = scenario.Payload with { AxiomClosure = default },
        };

        Assert.Null(Evaluate(scenario));
    }

    [Fact]
    public void Sl008AdmissionAllowsHistoricalAxiomClosureDifferenceWhenCurrentClosureIsStandard()
    {
        var scenario = CreateScenario("match");
        scenario = scenario with
        {
            ExpectedMaterial = scenario.ExpectedMaterial with
            {
                AxiomClosure = ["Quot.sound"],
            },
        };

        Assert.Null(Evaluate(scenario));
    }

    [Fact]
    public void Sl008AdmissionRejectsCurrentAxiomClosureOutsideStandardAllowlist()
    {
        var scenario = CreateScenario("match");
        scenario = scenario with
        {
            ExpectedMaterial = scenario.ExpectedMaterial with
            {
                AxiomClosure = ["Nonstandard.axiom"],
            },
        };

        var failure = Assert.IsType<FrozenLedgerAdmissionFailure>(Evaluate(scenario));

        Assert.Contains("standard axiom allowlist", failure.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("DeclarationStatementIds")]
    [InlineData("StatementId")]
    [InlineData("Input.DescriptorSelector")]
    public void Sl008DiagnosticNamesExpectedAndActualForEachComparedField(string field)
    {
        var scenario = CreateScenario(field);

        var failure = Assert.IsType<FrozenLedgerAdmissionFailure>(Evaluate(scenario));

        Assert.Contains(field + " expected=", failure.Message, StringComparison.Ordinal);
        Assert.Contains(scenario.ExpectedProbe, failure.Message, StringComparison.Ordinal);
        Assert.Contains(scenario.ActualProbe, failure.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("DeclarationStatementIds", "missing")]
    [InlineData("DeclarationStatementIds", "extra")]
    [InlineData("DeclarationStatementIds", "order")]
    public void Sl008SequenceDiagnosticIdentifiesTheConcreteDifference(string field, string shape)
    {
        var scenario = CreateSequenceScenario(field, shape);

        var failure = Assert.IsType<FrozenLedgerAdmissionFailure>(Evaluate(scenario));

        Assert.Contains(field + " expected=", failure.Message, StringComparison.Ordinal);
        Assert.Contains(scenario.ExpectedProbe, failure.Message, StringComparison.Ordinal);
        Assert.Contains(scenario.ActualProbe, failure.Message, StringComparison.Ordinal);
        Assert.Contains(scenario.ShapeProbe, failure.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("match")]
    [InlineData("DeclarationStatementIds")]
    [InlineData("StatementId")]
    [InlineData("WitnessId")]
    [InlineData("FrozenNodeId")]
    [InlineData("Input.DescriptorSelector")]
    [InlineData("all")]
    public void Sl008AdmissionDecisionMatchesTheRecordedSemanticPredicate(string mutation)
    {
        var scenario = CreateScenario(mutation);
        var expectedDecision = HistoricalActiveFreezeMatches(
            scenario.Payload,
            scenario.ExpectedMaterial);

        var failure = Evaluate(scenario);

        Assert.Equal(expectedDecision, failure is null);
    }

    [Fact]
    public void Sl008FieldDifferenceOrderingIsFixed()
    {
        var scenario = CreateScenario("all");

        var failure = Assert.IsType<FrozenLedgerAdmissionFailure>(Evaluate(scenario));

        var fields = new[]
        {
            "DeclarationStatementIds",
            "StatementId",
            "Input.DescriptorSelector",
        };
        var offsets = fields
            .Select(field => failure.Message.IndexOf(field + " expected=", StringComparison.Ordinal))
            .ToArray();
        Assert.All(offsets, static offset => Assert.True(offset >= 0));
        Assert.Equal(offsets.Order().ToArray(), offsets);
    }

    [Fact]
    public void Sl008FieldDifferenceDiagnosticIsByteDeterministic()
    {
        var scenario = CreateScenario("Input.DescriptorSelector");
        var expected =
            $"Active module {ModulePath} changed identity; append Revoke before rerunning ledger-append; "
            + "field differences: "
            + $"Input.DescriptorSelector expected={ModulePath}, actual={AlternateModulePath}; "
            + $"delta witness: {ModulePath}";

        var first = Assert.IsType<FrozenLedgerAdmissionFailure>(Evaluate(scenario));
        var second = Assert.IsType<FrozenLedgerAdmissionFailure>(Evaluate(scenario));

        Assert.Equal(expected, first.Message);
        Assert.Equal(expected, second.Message);
    }

    private static FrozenLedgerAdmissionFailure? Evaluate(DiagnosticScenario scenario)
    {
        var activeEntry = new FrozenActiveEntry(
            scenario.ActualMaterial,
            scenario.Payload,
            Sha256('f'));
        var activeEntries = ImmutableDictionary.CreateBuilder<string, FrozenActiveEntry>(
            StringComparer.Ordinal);
        activeEntries.Add(scenario.Payload.CaseId, activeEntry);
        foreach (var dependency in scenario.ActualDependencies)
        {
            var payload = PayloadFrom(dependency) with
            {
                CaseId = $"dependency-{dependency.FrozenNodeId.Value}",
            };
            activeEntries.Add(
                payload.CaseId,
                new FrozenActiveEntry(dependency, payload, Sha256('e')));
        }

        var baseView = new FrozenLedgerBaseView(
            new FrozenLedgerOrigin(FrozenLedgerTestData.GitOid('a'), FrozenLedgerTestData.GitOid('b')),
            [],
            activeEntries.ToImmutable(),
            activeEntries.Keys.ToImmutableHashSet(StringComparer.Ordinal),
            ImmutableHashSet<string>.Empty,
            ImmutableHashSet<string>.Empty);
        var preparation = new FrozenLedgerAdmissionPreparation(
            baseView,
            [],
            ImmutableHashSet<string>.Empty,
            TrustedFrozenGitReferences.CreateForTrustedAdapter([]));
        var changes = RawChangeSet.CreateWithKinds([(ModulePath, RawChangeKind.Modified)]);
        var scope = FrozenLedgerAdmissionScope.Create(
            changes,
            preparation,
            scenario.Catalog.States,
            scenario.Catalog.Adjacency);
        var expectedCatalog = FrozenMaterialCatalog.Create(
            scenario.Catalog.Environment,
            scenario.Catalog.States,
            [scenario.ExpectedMaterial, .. scenario.ExpectedDependencies],
            scenario.Catalog.OpenCases,
            scenario.Catalog.TailRegistrations);

        return FrozenLedger.ValidateAdmissionDelta(
            preparation,
            scope,
            expectedCatalog,
            preparation.TrustedDeltaReferences);
    }

    private static DiagnosticScenario CreateScenario(params string[] mutations)
    {
        var mutationSet = mutations.ToImmutableHashSet(StringComparer.Ordinal);
        var catalog = FrozenLedgerTestData.BuildCatalog(FrozenLedgerTestData.Module("A"));
        var actual = Assert.Single(catalog.ClosedNodes) with
        {
            DeclarationStatementIds =
            [
                Declaration("decl-a", '6'),
                Declaration("decl-b", '7'),
            ],
            StatementId = StatementId.Create(Sha256('1')),
            WitnessId = WitnessId.Create(Sha256('2')),
            FrozenNodeId = FrozenNodeId.Create(Sha256('3')),
            AxiomClosure = ["Classical.choice", "propext"],
            PrerequisiteFrozenNodeIds = [],
            Attestation = new FrozenModuleAttestation(
                RepoPath.CreateKnown(ModulePath),
                FrozenLedgerTestData.GitOid('1')),
        };
        var expected = actual;
        if (mutationSet.Contains("DeclarationStatementIds") || mutationSet.Contains("all"))
        {
            expected = expected with
            {
                DeclarationStatementIds =
                [
                    Declaration("decl-a", '6'),
                    Declaration("decl-c", 'a'),
                ],
            };
        }

        if (mutationSet.Contains("StatementId") || mutationSet.Contains("all"))
        {
            expected = expected with { StatementId = StatementId.Create(Sha256('b')) };
        }

        if (mutationSet.Contains("WitnessId") || mutationSet.Contains("all"))
        {
            expected = expected with { WitnessId = WitnessId.Create(Sha256('c')) };
        }

        if (mutationSet.Contains("FrozenNodeId") || mutationSet.Contains("all"))
        {
            expected = expected with { FrozenNodeId = FrozenNodeId.Create(Sha256('d')) };
        }

        if (mutationSet.Contains("PrerequisiteFrozenNodeIds") || mutationSet.Contains("all"))
        {
            expected = expected with
            {
                PrerequisiteFrozenNodeIds =
                [
                    FrozenNodeId.Create(Sha256('e')),
                    FrozenNodeId.Create(Sha256('f')),
                ],
            };
        }

        if (mutationSet.Contains("AxiomClosure") || mutationSet.Contains("all"))
        {
            expected = expected with
            {
                AxiomClosure = ["Quot.sound", "Classical.choice"],
            };
        }

        var payload = PayloadFrom(actual);
        if (mutationSet.Contains("Input.DescriptorSelector") || mutationSet.Contains("all"))
        {
            payload = payload with
            {
                Input = payload.Input with { DescriptorSelector = AlternateModulePath },
            };
        }

        var (expectedProbe, actualProbe) = ProbeFor(
            mutations.Length == 1 ? mutations[0] : "all",
            payload,
            expected);
        return new DiagnosticScenario(
            catalog,
            actual,
            expected,
            payload,
            expectedProbe,
            actualProbe,
            string.Empty);
    }

    private static FrozenNodeMaterial DependencyMaterial(string name, char identityDigit)
    {
        var path = RepoPath.CreateKnown($"D5/S0/Carrier/{name}.lean");
        return new FrozenNodeMaterial(
            path,
            [Declaration($"dependency-{name}", identityDigit)],
            StatementId.Create(Sha256(identityDigit)),
            WitnessId.Create(Sha256(identityDigit)),
            FrozenNodeId.Create(Sha256(identityDigit)),
            [],
            [],
            new FrozenModuleAttestation(path, FrozenLedgerTestData.GitOid(identityDigit)));
    }

    private static DiagnosticScenario CreateSequenceScenario(string field, string shape)
    {
        var scenario = CreateScenario("match");
        var expected = scenario.ExpectedMaterial;
        string expectedProbe;
        string actualProbe;
        string shapeProbe;
        if (field == "DeclarationStatementIds")
        {
            var actual = scenario.ActualMaterial.DeclarationStatementIds;
            var third = Declaration("decl-c", 'a');
            var sequence = shape switch
            {
                "missing" => actual.Add(third),
                "extra" => actual.RemoveAt(1),
                "order" => [actual[1], actual[0]],
                _ => throw new ArgumentOutOfRangeException(nameof(shape)),
            };
            expected = expected with { DeclarationStatementIds = sequence };
            expectedProbe = FormatDeclarations(sequence);
            actualProbe = FormatDeclarations(actual);
            shapeProbe = shape switch
            {
                "missing" => $"missing=[{FormatDeclaration(third)}]",
                "extra" => $"extra=[{FormatDeclaration(actual[1])}]",
                "order" => "order differs",
                _ => throw new ArgumentOutOfRangeException(nameof(shape)),
            };
        }
        else if (field == "AxiomClosure")
        {
            var actual = scenario.ActualMaterial.AxiomClosure;
            const string third = "Quot.sound";
            var sequence = shape switch
            {
                "missing" => actual.Add(third),
                "extra" => actual.RemoveAt(1),
                _ => throw new ArgumentOutOfRangeException(nameof(shape)),
            };
            expected = expected with { AxiomClosure = sequence };
            expectedProbe = FormatStrings(NormalizeAxiomClosure(sequence));
            actualProbe = FormatStrings(NormalizeAxiomClosure(actual));
            shapeProbe = shape switch
            {
                "missing" => $"missing=[{third}]",
                "extra" => $"extra=[{actual[1]}]",
                _ => throw new ArgumentOutOfRangeException(nameof(shape)),
            };
        }
        else
        {
            throw new ArgumentOutOfRangeException(nameof(field));
        }

        return scenario with
        {
            ExpectedMaterial = expected,
            ExpectedProbe = expectedProbe,
            ActualProbe = actualProbe,
            ShapeProbe = shapeProbe,
        };
    }

    private static FrozenFreezePayload PayloadFrom(FrozenNodeMaterial material) => new(
        "active-frozen",
        material.DeclarationStatementIds,
        material.FrozenNodeId,
        new FrozenLedgerInput(
            FrozenLedgerTestData.GitOid('a'),
            FrozenLedgerTestData.GitOid('b'),
            material.Attestation.SourceBlobOid,
            material.RepoPath.Value,
            []),
        material.PrerequisiteFrozenNodeIds,
        material.StatementId,
        material.WitnessId)
    {
        AxiomClosure = material.AxiomClosure,
    };

    private static bool HistoricalActiveFreezeMatches(
        FrozenFreezePayload payload,
        FrozenNodeMaterial material) =>
        payload.DeclarationStatementIds.SequenceEqual(material.DeclarationStatementIds)
        && payload.StatementId == material.StatementId
        && material.AxiomClosure.All(LeanAxiomFacts.IsStandard)
        && payload.Input.DescriptorSelector == material.RepoPath.Value;

    private static (string Expected, string Actual) ProbeFor(
        string field,
        FrozenFreezePayload payload,
        FrozenNodeMaterial material) => field switch
        {
            "DeclarationStatementIds" =>
                (FormatDeclarations(material.DeclarationStatementIds),
                    FormatDeclarations(payload.DeclarationStatementIds)),
            "StatementId" => (material.StatementId.Value, payload.StatementId.Value),
            "AxiomClosure" =>
                (FormatStrings(NormalizeAxiomClosure(material.AxiomClosure)),
                    FormatStrings(NormalizeAxiomClosure(payload.AxiomClosure))),
            "Input.DescriptorSelector" =>
                (material.RepoPath.Value, payload.Input.DescriptorSelector),
            _ => (material.StatementId.Value, payload.StatementId.Value),
        };

    private static FrozenDeclarationStatement Declaration(string key, char hashDigit) =>
        new(key, "theorem", StatementId.Create(Sha256(hashDigit)));

    private static string FormatDeclarations(IEnumerable<FrozenDeclarationStatement> declarations) =>
        "[" + string.Join(", ", declarations.Select(FormatDeclaration)) + "]";

    private static string FormatDeclaration(FrozenDeclarationStatement declaration) =>
        $"{declaration.DeclarationNameKey}|{declaration.Kind}|{declaration.StatementId.Value}";

    private static IEnumerable<string> NormalizeAxiomClosure(ImmutableArray<string> closure) =>
        closure.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal);

    private static string FormatStrings(IEnumerable<string> values) =>
        "[" + string.Join(", ", values) + "]";

    private static string Sha256(char digit) => $"sha256:{new string(digit, 64)}";

    private sealed record DiagnosticScenario(
        FrozenMaterialCatalog Catalog,
        FrozenNodeMaterial ActualMaterial,
        FrozenNodeMaterial ExpectedMaterial,
        FrozenFreezePayload Payload,
        string ExpectedProbe,
        string ActualProbe,
        string ShapeProbe)
    {
        internal ImmutableArray<FrozenNodeMaterial> ActualDependencies { get; init; } = [];

        internal ImmutableArray<FrozenNodeMaterial> ExpectedDependencies { get; init; } = [];
    }
}
