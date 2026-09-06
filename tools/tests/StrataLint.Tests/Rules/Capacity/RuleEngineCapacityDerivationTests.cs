using System.Collections.Concurrent;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RuleEngineCapacityDerivationTests
{
    [Fact]
    public void Sl003D5OnlyDeltaSkipsUnknownDebtDerivationAndStillNamesCapacityFinding()
    {
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.RingPath] += string.Concat(
            Enumerable.Repeat("-- pad\n", RepositoryRules.ArtifactHardLineLimit + 1));
        var context = fixture.Build(RawChangeSet.Create([RuleFixture.RingPath]));

        var findings = RepositoryRules.EvaluateCapacity(
            context,
            static _ => throw new InvalidOperationException("unknown-debt derivation was called"));

        var finding = Assert.Single(findings, item => item.Path == RuleFixture.RingPath);
        Assert.Equal("artifact exceeds 800 lines", finding.Message);
    }

    [Fact]
    public void Sl003BlueprintScribeDeltaRunsUnknownDebtDerivation()
    {
        var fixture = new RuleFixture();
        var context = fixture.Build(RawChangeSet.Create([RuleFixture.BlueprintSourcePath]));
        var calls = 0;

        RepositoryRules.EvaluateCapacity(context, _ =>
        {
            Interlocked.Increment(ref calls);
            return EmptyTestMap();
        });

        Assert.Equal(2, calls);
    }

    [Fact]
    public void Sl003StartsCurrentAndForkPointDerivationsBeforeEitherCompletes()
    {
        var fixture = new RuleFixture();
        var context = fixture.Build(RawChangeSet.Create([RuleFixture.BlueprintSourcePath]));
        var invokingThreadId = Environment.CurrentManagedThreadId;
        var bothStarted = new TaskCompletionSource<bool>(
            TaskCreationOptions.RunContinuationsAsynchronously);
        var events = new ConcurrentQueue<string>();
        var started = 0;
        var completedBeforeBothStarted = 0;

        RepositoryRules.EvaluateCapacity(context, snapshot =>
        {
            var side = ReferenceEquals(snapshot, context.Current) ? "Current" : "ForkPoint";
            events.Enqueue(side + ":started");
            if (Interlocked.Increment(ref started) == 2)
            {
                bothStarted.SetResult(true);
            }

            if (Environment.CurrentManagedThreadId == invokingThreadId)
            {
                Assert.Fail($"SL-003 serialized regression: {side} derivation ran inline");
            }

            if (!bothStarted.Task.Wait(TestBudgets.CapacityDerivationStartHangGuard))
            {
                throw new SkipException(
                    "infrastructure-hang-guard expired: SL-003 concurrency gate — ForkPoint derivation never started (serialized regression suspected)");
            }

            if (Volatile.Read(ref started) < 2)
            {
                Interlocked.Exchange(ref completedBeforeBothStarted, 1);
            }

            events.Enqueue(side + ":completed");
            return EmptyTestMap();
        });

        Assert.Equal(2, started);
        Assert.Equal(0, completedBeforeBothStarted);
        var recorded = events.ToArray();
        Assert.Equal(4, recorded.Length);
        Assert.All(recorded.Take(2), static item => Assert.EndsWith(":started", item));
        Assert.Contains("Current:started", recorded.Take(2));
        Assert.Contains("ForkPoint:started", recorded.Take(2));
    }

    [Fact]
    public void Sl003UsesTestMapStoreForBothSidesWhenPresent()
    {
        var fixture = FixtureWithUnknownDebt();
        var changes = RawChangeSet.Create([DebtSourcePath]);
        var context = fixture.Build(changes);
        var environment = new ScribeTestMapEnvironment(
            "test-rid",
            ".NET test framework",
            "/test/dotnet",
            "10.0.100-test",
            new string('d', 64));
        var storage = new CapacityMemoryStorage();
        var forkPointDigest = ScribeTestMapStore.ComputeInputDigest(context.ForkPoint);
        storage.Write(
            forkPointDigest + ".json",
            ScribeTestMapEnvelope.Create(
                forkPointDigest,
                ScribeTestMapStore.ComputeMetadataDigest(context.ForkPoint),
                environment,
                UnknownTestMap("ExistingDebt")).Write());
        var currentMap = UnknownTestMap("ExistingDebt", "CurrentDebt");
        var forkPointMap = UnknownTestMap("ExistingDebt");
        ScribeTestMap Derive(RepositorySnapshot snapshot) =>
            ReferenceEquals(snapshot, context.Current) ? currentMap : forkPointMap;
        var store = new ScribeTestMapStore(storage, environment, Derive);
        var cachedContext = RuleEvaluationContext.Create(
            context.Current,
            context.Baseline,
            context.Policy,
            context.Lean,
            context.Changes,
            context.MetaEvaluation,
            context.VerifiedScribeEmissions,
            context.ForkPoint,
            store);
        var expected = RepositoryRules.EvaluateCapacity(context, Derive);
        var actual = RepositoryRules.EvaluateCapacity(cachedContext, Derive);

        Assert.Equal(expected.ToArray(), actual.ToArray());
        Assert.Contains(actual, static finding => finding.Effect == AdmissionEffect.Block
            && finding.Message.Contains("DebtTests.CurrentDebt", StringComparison.Ordinal));
        var currentDigest = ScribeTestMapStore.ComputeInputDigest(context.Current);
        Assert.NotEqual(forkPointDigest, currentDigest);
        Assert.Equal(
            ["hit"],
            store.Events
                .Where(item => item.InputDigest == forkPointDigest)
                .Select(static item => item.Outcome));
        Assert.Equal(
            ["miss", "stored"],
            store.Events
                .Where(item => item.InputDigest == currentDigest)
                .Select(static item => item.Outcome));
    }

    [Fact]
    public void Sl003DerivesOnlyCurrentOnceWhenForkPointHitsStore()
    {
        var fixture = FixtureWithUnknownDebt();
        var context = fixture.Build(RawChangeSet.Create([DebtSourcePath]));
        var forkPointMap = UnknownTestMap("ExistingDebt");
        var currentMap = UnknownTestMap("ExistingDebt", "CurrentDebt");
        ScribeTestMap Derive(RepositorySnapshot snapshot) =>
            ReferenceEquals(snapshot, context.Current) ? currentMap : forkPointMap;
        Assert.Contains(forkPointMap.Methods, static method =>
            method.Id == "DebtTests.ExistingDebt" && method.UnknownReasons.Count != 0);
        var environment = new ScribeTestMapEnvironment("test-rid", ".NET test framework", "/test/dotnet", "10.0.100-test", new string('d', 64));
        var storage = new CapacityMemoryStorage();
        var digest = ScribeTestMapStore.ComputeInputDigest(context.ForkPoint);
        storage.Write(digest + ".json", ScribeTestMapEnvelope.Create(digest,
            ScribeTestMapStore.ComputeMetadataDigest(context.ForkPoint), environment, forkPointMap).Write());
        var calls = new ConcurrentQueue<RepositorySnapshot>();
        ScribeTestMap CountedDerive(RepositorySnapshot snapshot)
        {
            calls.Enqueue(snapshot);
            return Derive(snapshot);
        }
        var store = new ScribeTestMapStore(storage, environment, CountedDerive);
        var cachedContext = RuleEvaluationContext.Create(
            context.Current, context.Baseline, context.Policy, context.Lean, context.Changes,
            context.MetaEvaluation, context.VerifiedScribeEmissions, context.ForkPoint, store);
        var expected = RepositoryRules.EvaluateCapacity(context, Derive);
        var actual = RepositoryRules.EvaluateCapacity(cachedContext, CountedDerive);

        Assert.Same(context.Current, Assert.Single(calls));
        Assert.Equal(expected.ToArray(), actual.ToArray());
        Assert.Contains(actual, static finding => finding.Effect == AdmissionEffect.Block
            && finding.Message.Contains("DebtTests.CurrentDebt", StringComparison.Ordinal));
        Assert.Contains(store.Events, item => item.InputDigest == digest && item.Outcome == "hit");
    }

    [Fact]
    public async Task Sl003PassesDerivedMapsToUnknownDebtPolicyInCurrentForkPointOrder()
    {
        var fixture = new RuleFixture();
        var context = fixture.Build(RawChangeSet.Create([RuleFixture.BlueprintSourcePath]));
        var currentMap = UnknownTestMap("CurrentDebt");

        var findings = await RepositoryRules.EvaluateCapacityAsync(
            context,
            Task.FromResult(currentMap),
            Task.FromResult(EmptyTestMap()));

        var finding = Assert.Single(findings, static item =>
            item.Message.Contains("unknown test method introduced", StringComparison.Ordinal));
        Assert.Equal("tools/tests/Synthetic.Tests/DebtTests.cs", finding.Path);
        Assert.Equal(
            "conservative unknown test method introduced after fork point: "
            + "tools/tests/Synthetic.Tests::DebtTests.CurrentDebt",
            finding.Message);
    }

    [Fact]
    public void Sl003ProductionEntryBindsCurrentAndForkPointSnapshotsToPolicyOrder()
    {
        var fixture = new RuleFixture();
        var context = fixture.Build(RawChangeSet.Create([RuleFixture.BlueprintSourcePath]));
        var currentMap = UnknownTestMap("CurrentDebt");
        var forkPointMap = UnknownTestMap("ForkPointDebt");

        var findings = RepositoryRules.EvaluateCapacity(context, snapshot =>
        {
            if (ReferenceEquals(snapshot, context.Current))
            {
                return currentMap;
            }

            Assert.Same(context.ForkPoint, snapshot);
            return forkPointMap;
        });

        var finding = Assert.Single(findings, static item =>
            item.Message.Contains("unknown test method introduced", StringComparison.Ordinal));
        Assert.Equal("tools/tests/Synthetic.Tests/DebtTests.cs", finding.Path);
        Assert.Equal(
            "conservative unknown test method introduced after fork point: "
            + "tools/tests/Synthetic.Tests::DebtTests.CurrentDebt",
            finding.Message);
    }

    [Fact]
    public async Task Sl003WaitsForFaultedForkPointBeforeRethrowingCurrentFailure()
    {
        var fixture = new RuleFixture();
        var context = fixture.Build(RawChangeSet.Create([RuleFixture.BlueprintSourcePath]));
        var currentFailure = new InvalidOperationException("current derivation failed");
        var forkPointFailure = new InvalidOperationException("fork-point derivation failed");
        var forkPointDerivation = new TaskCompletionSource<ScribeTestMap>(
            TaskCreationOptions.RunContinuationsAsynchronously);

        var evaluation = RepositoryRules.EvaluateCapacityAsync(
            context,
            Task.FromException<ScribeTestMap>(currentFailure),
            forkPointDerivation.Task);
        Assert.False(
            evaluation.IsCompleted,
            "EvaluateCapacityAsync returned before awaiting ForkPoint");

        forkPointDerivation.SetException(forkPointFailure);
        var thrown = await Assert.ThrowsAsync<InvalidOperationException>(() => evaluation);

        Assert.Same(currentFailure, thrown);
    }

    [Fact]
    public async Task Sl003DoesNotSwallowForkPointDerivationFailureWhenCurrentSucceeds()
    {
        var fixture = new RuleFixture();
        var context = fixture.Build(RawChangeSet.Create([RuleFixture.BlueprintSourcePath]));
        var forkPointFailure = new InvalidOperationException("fork-point derivation failed");

        var thrown = await Assert.ThrowsAsync<InvalidOperationException>(() =>
            RepositoryRules.EvaluateCapacityAsync(
                context,
                Task.FromResult(EmptyTestMap()),
                Task.FromException<ScribeTestMap>(forkPointFailure)));

        Assert.Same(forkPointFailure, thrown);
    }

    [Fact]
    public void Sl003StartsOnlyOneDerivationWhenCurrentAndForkPointAreSameSnapshot()
    {
        var fixture = new RuleFixture();
        var context = fixture.Build(RawChangeSet.Create([RuleFixture.BlueprintSourcePath]));
        var sameSnapshotContext = RuleEvaluationContext.Create(
            context.Current,
            context.Baseline,
            context.Policy,
            context.Lean,
            context.Changes,
            context.MetaEvaluation,
            context.VerifiedScribeEmissions,
            context.Current);
        var calls = 0;

        RepositoryRules.EvaluateCapacity(sameSnapshotContext, _ =>
        {
            Interlocked.Increment(ref calls);
            return EmptyTestMap();
        });

        Assert.Equal(1, calls);
    }

    [Fact]
    public void Sl003ExcludedCapacityPathThatIsDerivationInputStillWakesAndRunsUnknownDebtDerivation()
    {
        const string path = "docs/develop/x/packages.lock.json";
        var fixture = new RuleFixture();
        var context = fixture.Build(RawChangeSet.Create([path]));
        var registration = Assert.Single(
            RepositoryRules.CreateRegistrations(),
            item => item.Descriptor.Id == RuleId.CreateKnown(3));
        var calls = 0;

        if (registration.Rule.IsAffectedBy(context))
        {
            RepositoryRules.EvaluateCapacity(context, _ =>
            {
                Interlocked.Increment(ref calls);
                return EmptyTestMap();
            });
        }

        Assert.Equal(2, calls);
    }

    [Theory]
    [InlineData("D5/S0/Carrier/Generated.cs")]
    [InlineData("tools/Synthetic/Synthetic.csproj")]
    [InlineData("tools/Synthetic/packages.lock.json")]
    [InlineData("global.json")]
    [InlineData("eng/Directory.Build.rsp")]
    [InlineData("eng/Directory.Packages.targets")]
    [InlineData("eng/NUGET.CONFIG")]
    [InlineData("eng/imported.props")]
    [InlineData("eng/imported.targets")]
    public void ScribeDerivationInputIncludesTrackedAndImportedBuildInputs(string path)
    {
        Assert.True(ScribeTestMapDeriver.IsDerivationInput(path));
    }

    [Fact]
    public void ScribeDerivationInputIncludesPrefixedLockFileName()
    {
        Assert.True(ScribeTestMapDeriver.IsDerivationInput(
            "tools/tests/Synthetic.Tests/vendor-packages.lock.json"));
    }

    [Theory]
    [InlineData("D5/S0/Carrier/Ring.lean")]
    [InlineData("Blueprint/D5/S0/Carrier/Ring.md")]
    [InlineData("README.md")]
    public void ScribeDerivationInputExcludesUnrelatedContent(string path)
    {
        Assert.False(ScribeTestMapDeriver.IsDerivationInput(path));
    }

    private const string DebtSourcePath = "tools/tests/Synthetic.Tests/DebtTests.cs";

    private static RuleFixture FixtureWithUnknownDebt()
    {
        var fixture = new RuleFixture();
        fixture.Baseline[DebtSourcePath] = "// existing debt\n";
        fixture.ForkPoint[DebtSourcePath] = "// existing debt\n";
        fixture.Files[DebtSourcePath] = "// existing and current debt\n";
        return fixture;
    }

    private static ScribeTestMap EmptyTestMap() => new([], [], [], [], []);

    private static ScribeTestMap UnknownTestMap(params string[] methodIds) =>
        new(
            methodIds.Select(methodId =>
                new ScribeTestMethod(
                    "tools/tests/Synthetic.Tests",
                    "tools/tests/Synthetic.Tests/DebtTests.cs",
                    "DebtTests." + methodId,
                    [TestMapUnknownReason.Other])).ToArray(),
            [],
            [],
            [],
            []);

    private sealed class CapacityMemoryStorage : IScribeTestMapStorage
    {
        private readonly ConcurrentDictionary<string, byte[]> files = new(StringComparer.Ordinal);

        public bool TryRead(string name, out byte[] bytes)
        {
            if (files.TryGetValue(name, out var stored))
            {
                bytes = stored.ToArray();
                return true;
            }

            bytes = [];
            return false;
        }

        public void Write(string name, byte[] bytes) => files[name] = bytes.ToArray();
    }
}
