using System.Collections.Immutable;
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
        var registrations = Enumerable.Range(1, 23).Append(25).Append(26).Append(28)
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
        Assert.Equal(descriptors.Select(static descriptor => descriptor.Id), completed.ExecutedRules);
        Assert.Empty(completed.DeferredRules);
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
    public void RuleCatalogDoesNotInvokeRulesUnaffectedByTheCandidateDelta()
    {
        var rule = new CountingUnaffectedRule();
        var registrations = Enumerable.Range(1, 23).Append(25).Append(26).Append(28)
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
            registrations.Select(static registration => registration.Descriptor.Id),
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
            "sha256:beff7d95d79f7e452713fb1b5adfb4bf1a2ce8323687a30079962d97ae389cec",
            RuleCatalog.Default.RootSha256);
    }

    private static RuleDescriptor Descriptor(
        int number,
        string title,
        DisplaySeverity displaySeverity,
        AdmissionEffect admissionEffect) =>
        new(
            RuleId.CreateKnown(number),
            title,
            displaySeverity,
            $"category-{number}",
            admissionEffect,
            RuleLifecycle.Active,
            null);

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
}
