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
        var serialInvocationDetected = new TaskCompletionSource<bool>(
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
                serialInvocationDetected.SetResult(true);
            }

            var openedGate = Task.WhenAny(bothStarted.Task, serialInvocationDetected.Task)
                .GetAwaiter()
                .GetResult();
            Assert.Same(bothStarted.Task, openedGate);
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
    public async Task Sl003PrefersCurrentFailureAfterObservingBothDerivationFailures()
    {
        var fixture = new RuleFixture();
        var context = fixture.Build(RawChangeSet.Create([RuleFixture.BlueprintSourcePath]));
        var currentFailure = new InvalidOperationException("current derivation failed");
        var forkPointFailure = new InvalidOperationException("fork-point derivation failed");
        var currentTask = Task.FromException<ScribeTestMap>(currentFailure);
        var forkPointTask = Task.FromException<ScribeTestMap>(forkPointFailure);

        var thrown = await Assert.ThrowsAsync<InvalidOperationException>(() =>
            RepositoryRules.EvaluateCapacityAsync(context, currentTask, forkPointTask));

        Assert.Same(currentFailure, thrown);
        var observedForkPointFailure = Assert.IsType<AggregateException>(forkPointTask.Exception);
        Assert.Same(forkPointFailure, Assert.Single(observedForkPointFailure.InnerExceptions));
    }

    [Fact]
    public async Task Sl003WaitsForForkPointTerminationBeforeReturningCurrentFailure()
    {
        var fixture = new RuleFixture();
        var context = fixture.Build(RawChangeSet.Create([RuleFixture.BlueprintSourcePath]));
        var currentFailure = new InvalidOperationException("current derivation failed");
        var forkPointFailure = new InvalidOperationException("fork-point derivation failed");
        var forkPointDerivation = new TaskCompletionSource<ScribeTestMap>(
            TaskCreationOptions.RunContinuationsAsynchronously);
        var evaluationReturned = new TaskCompletionSource<bool>(
            TaskCreationOptions.RunContinuationsAsynchronously);

        var evaluation = RepositoryRules.EvaluateCapacityAsync(
            context,
            Task.FromException<ScribeTestMap>(currentFailure),
            forkPointDerivation.Task);
        var returnObserver = evaluation.ContinueWith(
            static (_, state) =>
            {
                ((TaskCompletionSource<bool>)state!).SetResult(true);
            },
            evaluationReturned,
            CancellationToken.None,
            TaskContinuationOptions.ExecuteSynchronously,
            TaskScheduler.Default);

        var returnedBeforeForkPointTerminated = evaluationReturned.Task.IsCompleted;
        forkPointDerivation.SetException(forkPointFailure);

        var thrown = await Assert.ThrowsAsync<InvalidOperationException>(() => evaluation);
        await returnObserver;
        var observedForkPointFailure = Assert.IsType<AggregateException>(
            forkPointDerivation.Task.Exception);

        Assert.False(
            returnedBeforeForkPointTerminated,
            "EvaluateCapacityAsync returned before the ForkPoint derivation reached a terminal state");
        Assert.Same(currentFailure, thrown);
        Assert.Same(forkPointFailure, Assert.Single(observedForkPointFailure.InnerExceptions));
        Assert.True(evaluationReturned.Task.IsCompletedSuccessfully);
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

    private static ScribeTestMap EmptyTestMap() => new([], [], [], [], []);

    private static ScribeTestMap UnknownTestMap(string methodId) =>
        new(
            [
                new ScribeTestMethod(
                    "tools/tests/Synthetic.Tests",
                    "tools/tests/Synthetic.Tests/DebtTests.cs",
                    "DebtTests." + methodId,
                    [TestMapUnknownReason.Other]),
            ],
            [],
            [],
            [],
            []);
}
