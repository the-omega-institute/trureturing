using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RuleCatalogAssociationTests
{
    [Fact]
    public void CatalogStoresEachDescriptorAndRuleInOneTypedRegistration()
    {
        var fields = typeof(RuleCatalog).GetFields(
            System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic);

        Assert.DoesNotContain(
            fields,
            field => field.FieldType == typeof(ImmutableArray<IRepositoryRule>));
        Assert.Single(fields, static field =>
        {
            if (!field.FieldType.IsGenericType
                || field.FieldType.GetGenericTypeDefinition() != typeof(ImmutableArray<>))
            {
                return false;
            }

            var elementType = field.FieldType.GetGenericArguments()[0];
            return elementType.GetProperty("Descriptor")?.PropertyType == typeof(RuleDescriptor)
                && elementType.GetProperty("Rule")?.PropertyType == typeof(IRepositoryRule);
        });
    }

    [Fact]
    public void EveryActiveRepositoryRuleDeclaresAnAffectedClosure()
    {
        var affectedPredicateType = typeof(Func<RuleEvaluationContext, bool>);
        var active = RepositoryRules.CreateRegistrations()
            .Where(static registration => registration.Descriptor.Lifecycle is RuleLifecycle.Active);

        foreach (var registration in active)
        {
            var predicateField = registration.Rule.GetType()
                .GetFields(System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic)
                .SingleOrDefault(field => field.FieldType == affectedPredicateType);
            Assert.True(
                predicateField?.GetValue(registration.Rule) is not null,
                $"{registration.Descriptor.Id.Value} has no explicit affected closure");
        }
    }

    [Fact]
    public void EvaluateSingleStampsFindingsWithTheDescriptorPairedToTheSelectedRule()
    {
        var firstDescriptor = Descriptor(
            1,
            "first descriptor",
            DisplaySeverity.Warning,
            AdmissionEffect.Observe);
        var secondDescriptor = Descriptor(
            2,
            "second descriptor",
            DisplaySeverity.Error,
            AdmissionEffect.Block);
        var catalog = RuleCatalog.CreateForTesting(
            [
                Registration(
                    firstDescriptor,
                    FindingRule("first/path.txt", "finding from first rule")),
                Registration(
                    secondDescriptor,
                    FindingRule("second/path.txt", "finding from second rule")),
            ]);
        var context = new RuleFixture().Build();

        var first = Assert.Single(catalog.EvaluateSingle(firstDescriptor.Id, context).Diagnostics);
        var second = Assert.Single(catalog.EvaluateSingle(secondDescriptor.Id, context).Diagnostics);

        Assert.Equal(
            new Diagnostic(
                firstDescriptor.Id,
                firstDescriptor.Title,
                firstDescriptor.DisplaySeverity,
                firstDescriptor.AdmissionEffect,
                "first/path.txt",
                "finding from first rule"),
            first);
        Assert.Equal(
            new Diagnostic(
                secondDescriptor.Id,
                secondDescriptor.Title,
                secondDescriptor.DisplaySeverity,
                secondDescriptor.AdmissionEffect,
                "second/path.txt",
                "finding from second rule"),
            second);
    }

    [Fact]
    public void ExecuteStampsAUniqueFindingWithItsPairedDescriptorAcrossACompleteCatalog()
    {
        var uniqueFinding = new RuleFinding("unique/path.txt", "finding from rule seventeen");
        var registrations = Enumerable.Range(1, 23).Except([5])
            .Append(25).Append(26).Append(28)
            .Select(number => new RuleRegistration(
                Descriptor(
                    number,
                    $"descriptor {number}",
                    number == 17 ? DisplaySeverity.Warning : DisplaySeverity.Error,
                    number == 17 ? AdmissionEffect.Observe : AdmissionEffect.Block),
                new FakeRule(
                    static _ => false,
                    number == 17
                        ? ImmutableArray.Create(uniqueFinding)
                        : ImmutableArray<RuleFinding>.Empty)))
            .ToImmutableArray();
        var descriptors = registrations
            .Select(static registration => registration.Descriptor)
            .ToImmutableArray();
        var catalog = RuleCatalog.CreateForTesting(registrations);

        var outcome = catalog.Execute(new RuleFixture().Build());

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(outcome).Capability;
        Assert.Equal(
            descriptors
                .Where(static descriptor => descriptor.Lifecycle is RuleLifecycle.Active)
                .Select(static descriptor => descriptor.Id),
            completed.ExecutedRules);
        Assert.Equal(
            descriptors
                .Where(static descriptor => descriptor.Lifecycle is RuleLifecycle.Deferred)
                .Select(static descriptor => descriptor.Id),
            completed.DeferredRules.Select(static deferred => deferred.RuleId));
        Assert.Equal(
            new Diagnostic(
                RuleId.CreateKnown(17),
                "descriptor 17",
                DisplaySeverity.Warning,
                AdmissionEffect.Observe,
                uniqueFinding.Path,
                uniqueFinding.Message),
            Assert.Single(completed.Diagnostics));
    }

    [Fact]
    public void MeasureRuleObservesTheDefinedExecutionOrder()
    {
        var measured = ImmutableArray.CreateBuilder<RuleId>();
        var context = new RuleFixture().Build(RawChangeSet.Create(
            ["tools/StrataLint.Engine/Rules/RepositoryRules.cs"]));

        var outcome = RuleCatalog.Default.Execute(
            context,
            (ruleId, _, evaluate) =>
            {
                measured.Add(ruleId);
                return evaluate();
            });

        Assert.IsType<RuleExecutionOutcome.Completed>(outcome);
        Assert.Equal(
            RuleCatalog.ExecutionOrder.Select(static id => id.Value),
            measured.Select(static id => id.Value));
    }

    [Fact]
    public void ExecutionOrderIsAnExactNonDuplicatedPermutationOfActiveRegistrations()
    {
        var activeIds = RepositoryRules.CreateRegistrations()
            .Where(static registration => registration.Descriptor.Lifecycle is RuleLifecycle.Active)
            .Select(static registration => registration.Descriptor.Id)
            .ToImmutableArray();
        var executionOrder = RuleCatalog.ExecutionOrder;

        Assert.DoesNotContain(activeIds.GroupBy(static id => id), static group => group.Count() > 1);
        Assert.DoesNotContain(executionOrder.GroupBy(static id => id), static group => group.Count() > 1);
        Assert.Empty(activeIds.Except(executionOrder));
        Assert.Empty(executionOrder.Except(activeIds));
    }

    [Fact]
    public void CanonicalAndPriorityExecutionProduceEquivalentCompletedRuleSets()
    {
        var canonicalOrder = RepositoryRules.CreateRegistrations()
            .Where(static registration => registration.Descriptor.Lifecycle is RuleLifecycle.Active)
            .Select(static registration => registration.Descriptor.Id)
            .ToImmutableArray();
        var priorityOrder = RuleCatalog.ExecutionOrder;
        Assert.False(
            canonicalOrder.SequenceEqual(priorityOrder),
            $"Priority order [{string.Join(',', priorityOrder)}] must differ from canonical order "
            + $"[{string.Join(',', canonicalOrder)}] for this equivalence test to carry evidence.");

        var observedDiagnostics = false;
        var observedExecutedInversion = false;
        foreach (var scenario in new[] { "baseline", "badge", "sorry", "shared-rule-implementation" })
        {
            var canonical = ExecuteProductionInFreshWorld(scenario, canonicalOrder).Completed;
            var priority = ExecuteProductionInFreshWorld(scenario, priorityOrder).Completed;

            AssertEquivalentCompletedRuleSets(canonical, priority);
            observedDiagnostics |= !canonical.Diagnostics.IsEmpty;
            observedExecutedInversion |=
                ContainsPartitionOrderInversion(canonicalOrder, priorityOrder, canonical.ExecutedRules);
        }

        Assert.True(observedDiagnostics, "The production scenarios must exercise at least one diagnostic.");
        Assert.True(
            observedExecutedInversion,
            "At least one executed partition must contain a canonical-to-priority inversion.");
    }

    [Fact]
    public void EquivalenceAssertionRejectsOrderDependentRulesWithFreshState()
    {
        var setterId = RuleId.CreateKnown(1);
        var finderId = RuleId.CreateKnown(2);
        var remainingIds = Enumerable.Range(1, 23).Except([5, 7, 9, 13, 14])
            .Append(25).Append(26).Append(28)
            .Select(RuleId.CreateKnown)
            .Where(id => id != setterId && id != finderId)
            .ToImmutableArray();
        ImmutableArray<RuleId> setterFirstOrder = [setterId, finderId, .. remainingIds];
        ImmutableArray<RuleId> finderFirstOrder = [finderId, setterId, .. remainingIds];
        var setterFirst = ExecuteOrderDependentRulesInFreshWorld(setterFirstOrder);
        var finderFirst = ExecuteOrderDependentRulesInFreshWorld(finderFirstOrder);

        Assert.Empty(setterFirst.Diagnostics);
        Assert.Single(finderFirst.Diagnostics);
        var failure = Record.Exception(() => AssertEquivalentCompletedRuleSets(setterFirst, finderFirst));
        Assert.NotNull(failure);
        Assert.IsAssignableFrom<Xunit.Sdk.XunitException>(failure);
    }

    [Fact]
    public void ExecutionOrderDoesNotChangeCertificateFingerprintOrCatalogRoot()
    {
        var canonicalOrder = RepositoryRules.CreateRegistrations()
            .Where(static registration => registration.Descriptor.Lifecycle is RuleLifecycle.Active)
            .Select(static registration => registration.Descriptor.Id)
            .ToImmutableArray();
        var canonicalRun = ExecuteProductionInFreshWorld("baseline", canonicalOrder);
        var priorityRun = ExecuteProductionInFreshWorld("baseline", RuleCatalog.ExecutionOrder);
        var canonical = CanonicalFixedPoint.Create([1, 2, 3], "registry-fixture");

        var canonicalCertificate = AdmissionCertificate.Create(canonical, canonicalRun.Completed);
        var priorityCertificate = AdmissionCertificate.Create(canonical, priorityRun.Completed);

        Assert.Equal(
            Encoding.UTF8.GetBytes(canonicalCertificate.Fingerprint),
            Encoding.UTF8.GetBytes(priorityCertificate.Fingerprint));
        Assert.Equal(canonicalRun.Catalog.RootSha256, priorityRun.Catalog.RootSha256);
        Assert.Equal<RuleDescriptor>(
            canonicalRun.Catalog.Descriptors,
            priorityRun.Catalog.Descriptors);
    }

    [Fact]
    public void RuleCatalogDoesNotInvokeRulesUnaffectedByTheCandidateDelta()
    {
        var rule = new CountingUnaffectedRule();
        var registrations = Enumerable.Range(1, 23).Except([5])
            .Append(25).Append(26).Append(28)
            .Select(number => Registration(
                Descriptor(
                    number,
                    $"descriptor {number}",
                    DisplaySeverity.Error,
                    AdmissionEffect.Block),
                rule))
            .ToImmutableArray();
        var catalog = RuleCatalog.CreateForTesting(registrations);

        var outcome = catalog.Execute(new RuleFixture().Build());

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(outcome).Capability;
        Assert.Equal(0, rule.EvaluationCount);
        Assert.Empty(completed.ExecutedRules);
        var skippedProperty = typeof(CompletedRuleSet).GetProperty("SkippedRules");
        Assert.NotNull(skippedProperty);
        var skipped = Assert.IsType<ImmutableArray<RuleId>>(skippedProperty!.GetValue(completed));
        Assert.Equal(
            registrations
                .Where(static registration => registration.Descriptor.Lifecycle is RuleLifecycle.Active)
                .Select(static registration => registration.Descriptor.Id),
            skipped);
    }

    [Theory]
    [InlineData("tools/StrataLint.Engine/Rules/RepositoryRules.cs")]
    [InlineData("tools/StrataLint.Engine/Rules/FutureSharedRule.cs")]
    [InlineData("tools/StrataLint.Engine/Ledger/FrozenAcceptedEventLoader.cs")]
    [InlineData("tools/StrataLint.Engine/Revocation/TrustedRevocationReceipts.cs")]
    [InlineData("tools/StrataLint.Engine/StrataLint.Engine.csproj")]
    [InlineData("Directory.Build.targets")]
    public void EveryActiveRuleWakesWhenSharedRuleImplementationChanges(string changedPath)
    {
        var context = new RuleFixture().Build(RawChangeSet.Create([changedPath]));

        var outcome = RuleCatalog.Default.Execute(context);

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(outcome).Capability;
        var active = RuleCatalog.Default.Descriptors
            .Where(static descriptor => descriptor.Lifecycle == RuleLifecycle.Active)
            .Select(static descriptor => descriptor.Id);
        Assert.Equal(active, completed.ExecutedRules);
        Assert.Empty(completed.SkippedRules);
    }

    [Fact]
    public void NonRuleEngineSourceChangeRetainsPerRuleScoping()
    {
        var context = new RuleFixture().Build(RawChangeSet.Create(
            ["tools/StrataLint.Engine/Snapshot/CanonicalSnapshot.cs"]));

        var outcome = RuleCatalog.Default.Execute(context);

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(outcome).Capability;
        Assert.NotEmpty(completed.ExecutedRules);
        Assert.NotEmpty(completed.SkippedRules);
    }

    [Fact]
    public void ApplicableToPreservesPairAssociationsAndCatalogOrder()
    {
        const string firstPath = "association/first.txt";
        const string secondPath = "association/second.txt";
        const string sharedPath = "association/shared.txt";
        var fixture = new RuleFixture();
        fixture.Files[firstPath] = "first\n";
        fixture.Files[secondPath] = "second\n";
        fixture.Files[sharedPath] = "shared\n";
        var evaluationContext = fixture.Build();
        var applicabilityContext = RuleApplicabilityContext.Create(
            evaluationContext.Current,
            evaluationContext.Policy);
        var firstDescriptor = Descriptor(
            1,
            "first descriptor",
            DisplaySeverity.Warning,
            AdmissionEffect.Observe);
        var secondDescriptor = Descriptor(
            2,
            "second descriptor",
            DisplaySeverity.Error,
            AdmissionEffect.Block);
        var firstRule = PredicateRule(path => path is firstPath or sharedPath);
        var secondRule = PredicateRule(path => path is secondPath or sharedPath);
        var forward = RuleCatalog.CreateForTesting(
            [Registration(firstDescriptor, firstRule), Registration(secondDescriptor, secondRule)]);
        var reordered = RuleCatalog.CreateForTesting(
            [Registration(secondDescriptor, secondRule), Registration(firstDescriptor, firstRule)]);

        Assert.Equal(
            new[] { firstDescriptor },
            forward.ApplicableTo(Artifact(evaluationContext, firstPath), applicabilityContext));
        Assert.Equal(
            new[] { secondDescriptor },
            forward.ApplicableTo(Artifact(evaluationContext, secondPath), applicabilityContext));
        Assert.Equal(
            new[] { firstDescriptor, secondDescriptor },
            forward.ApplicableTo(Artifact(evaluationContext, sharedPath), applicabilityContext));

        Assert.Equal(
            new[] { firstDescriptor },
            reordered.ApplicableTo(Artifact(evaluationContext, firstPath), applicabilityContext));
        Assert.Equal(
            new[] { secondDescriptor },
            reordered.ApplicableTo(Artifact(evaluationContext, secondPath), applicabilityContext));
        Assert.Equal(
            new[] { secondDescriptor, firstDescriptor },
            reordered.ApplicableTo(Artifact(evaluationContext, sharedPath), applicabilityContext));
    }

    [Fact]
    public void DescriptorProjectionAndCatalogRootDependOnlyOnOrderedDescriptors()
    {
        var firstDescriptor = Descriptor(
            1,
            "first descriptor",
            DisplaySeverity.Warning,
            AdmissionEffect.Observe);
        var secondDescriptor = Descriptor(
            2,
            "second descriptor",
            DisplaySeverity.Error,
            AdmissionEffect.Block);
        var descriptors = ImmutableArray.Create(firstDescriptor, secondDescriptor);
        var first = RuleCatalog.CreateForTesting(
            [
                Registration(firstDescriptor, PredicateRule(static _ => true)),
                Registration(secondDescriptor, PredicateRule(static _ => false)),
            ]);
        var differentRules = RuleCatalog.CreateForTesting(
            [
                Registration(
                    firstDescriptor,
                    FindingRule("different/first.txt", "different first finding")),
                Registration(
                    secondDescriptor,
                    FindingRule("different/second.txt", "different second finding")),
            ]);
        var reordered = RuleCatalog.CreateForTesting(
            [
                Registration(secondDescriptor, PredicateRule(static _ => false)),
                Registration(firstDescriptor, PredicateRule(static _ => true)),
            ]);

        Assert.Equal(new[] { firstDescriptor, secondDescriptor }, first.Descriptors);
        Assert.Equal(first.RootSha256, differentRules.RootSha256);
        Assert.Equal(new[] { secondDescriptor, firstDescriptor }, reordered.Descriptors);
        Assert.NotEqual(first.RootSha256, reordered.RootSha256);
    }

    [Fact]
    public void DefaultCatalogRootMatchesCharacterizedRegressionValue()
    {
        Assert.Equal(
            "sha256:f2d40856963228076208b95d0c0450d2cae79d653dce07f1a7d445437ca10ae4",
            RuleCatalog.Default.RootSha256);
    }

    private static CompletedRuleSet Completed(RuleExecutionOutcome outcome) =>
        Assert.IsType<RuleExecutionOutcome.Completed>(outcome).Capability;

    private static (RuleCatalog Catalog, CompletedRuleSet Completed) ExecuteProductionInFreshWorld(
        string scenario,
        ImmutableArray<RuleId> executionOrder)
    {
        var registrations = RepositoryRules.CreateRegistrations();
        var catalog = RuleCatalog.CreateForTesting(registrations);
        var fixture = new RuleFixture();
        RuleEvaluationContext context;
        if (scenario == "shared-rule-implementation")
        {
            context = fixture.Build(RawChangeSet.Create(
                ["tools/StrataLint.Engine/Rules/RepositoryRules.cs"]));
        }
        else
        {
            if (scenario != "baseline")
            {
                fixture.Apply(scenario);
            }

            context = fixture.Build();
        }

        return (catalog, Completed(catalog.ExecuteInOrderForTesting(context, executionOrder)));
    }

    private static CompletedRuleSet ExecuteOrderDependentRulesInFreshWorld(
        ImmutableArray<RuleId> executionOrder)
    {
        var state = new OrderDependentState();
        var registrations = Enumerable.Range(1, 23).Except([5])
            .Append(25).Append(26).Append(28)
            .Select(number => new RuleRegistration(
                Descriptor(number, $"descriptor {number}", DisplaySeverity.Error, AdmissionEffect.Block),
                number switch
                {
                    1 => new StateSettingRule(state),
                    2 => new FindingWhileStateUnsetRule(state),
                    _ => new FakeRule(static _ => false, []),
                }))
            .ToImmutableArray();
        var catalog = RuleCatalog.CreateForTesting(registrations);
        var context = new RuleFixture().Build(RawChangeSet.Create(
            ["tools/StrataLint.Engine/Rules/RepositoryRules.cs"]));
        return Completed(catalog.ExecuteInOrderForTesting(context, executionOrder));
    }

    private static void AssertEquivalentCompletedRuleSets(
        CompletedRuleSet canonical,
        CompletedRuleSet priority)
    {
        Assert.Equal<Diagnostic>(NormalizeDiagnostics(canonical), NormalizeDiagnostics(priority));
        Assert.Equal(
            canonical.DeferredRules.Select(static rule =>
                $"{rule.RuleId.Value}:{rule.CaseId.Value}:{rule.Title}"),
            priority.DeferredRules.Select(static rule =>
                $"{rule.RuleId.Value}:{rule.CaseId.Value}:{rule.Title}"));
        Assert.Equal(
            canonical.ExecutedRules.Select(static id => id.Value),
            priority.ExecutedRules.Select(static id => id.Value));
        Assert.Equal(
            canonical.SkippedRules.Select(static id => id.Value),
            priority.SkippedRules.Select(static id => id.Value));
    }

    private static bool ContainsPartitionOrderInversion(
        ImmutableArray<RuleId> canonicalOrder,
        ImmutableArray<RuleId> priorityOrder,
        ImmutableArray<RuleId> partition)
    {
        var partitionIds = partition.ToImmutableHashSet();
        return !canonicalOrder.Where(partitionIds.Contains)
            .SequenceEqual(priorityOrder.Where(partitionIds.Contains));
    }

    private static ImmutableArray<Diagnostic> NormalizeDiagnostics(CompletedRuleSet completed) =>
        completed.Diagnostics
            .OrderBy(static diagnostic => diagnostic.RuleId.Value, StringComparer.Ordinal)
            .ThenBy(static diagnostic => diagnostic.Path, StringComparer.Ordinal)
            .ThenBy(static diagnostic => diagnostic.Message, StringComparer.Ordinal)
            .ToImmutableArray();

    private static RuleDescriptor Descriptor(
        int number,
        string title,
        DisplaySeverity displaySeverity,
        AdmissionEffect admissionEffect)
    {
        var deferredCase = number is 7 or 9 or 13 or 14
            ? CaseId.CreateKnown($"D5-T{number:0000}")
            : null;
        return new(
            RuleId.CreateKnown(number),
            title,
            displaySeverity,
            $"category-{number}",
            admissionEffect,
            deferredCase is null ? RuleLifecycle.Active : RuleLifecycle.Deferred,
            deferredCase);
    }

    private static IRepositoryRule FindingRule(string path, string message) =>
        new FakeRule(static _ => false, [new RuleFinding(path, message)]);

    private static RuleRegistration Registration(
        RuleDescriptor descriptor,
        IRepositoryRule rule) =>
        new(descriptor, rule);

    private static IRepositoryRule PredicateRule(Func<string, bool> predicate) =>
        new FakeRule(file => predicate(file.Path.Value), ImmutableArray<RuleFinding>.Empty);

    private static RepositoryFile Artifact(RuleEvaluationContext context, string path) =>
        context.Current.Files.Single(pair => pair.Key.Value == path).Value;

    private sealed class FakeRule(
        Func<RepositoryFile, bool> appliesTo,
        ImmutableArray<RuleFinding> findings) : IRepositoryRule
    {
        public bool AppliesTo(RepositoryFile artifact, RuleApplicabilityContext context) =>
            appliesTo(artifact);

        public ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context) => findings;
    }

    private sealed class CountingUnaffectedRule : IRepositoryRule
    {
        internal int EvaluationCount { get; private set; }

        public bool AppliesTo(RepositoryFile artifact, RuleApplicabilityContext context) => false;

        public bool IsAffectedBy(RuleEvaluationContext context) => false;

        public ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context)
        {
            EvaluationCount++;
            return [];
        }
    }

    private sealed class OrderDependentState
    {
        internal bool IsSet { get; set; }
    }

    private sealed class StateSettingRule(OrderDependentState state) : IRepositoryRule
    {
        public bool AppliesTo(RepositoryFile artifact, RuleApplicabilityContext context) => true;

        public ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context)
        {
            state.IsSet = true;
            return [];
        }
    }

    private sealed class FindingWhileStateUnsetRule(OrderDependentState state) : IRepositoryRule
    {
        public bool AppliesTo(RepositoryFile artifact, RuleApplicabilityContext context) => true;

        public ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context) =>
            state.IsSet
                ? []
                : [new RuleFinding("synthetic/order-dependent.txt", "state was unset")];
    }
}
