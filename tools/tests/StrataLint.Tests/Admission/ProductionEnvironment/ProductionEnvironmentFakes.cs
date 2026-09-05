using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

// 这三个 Fake 是被 32 / 30 / 21 个测试文件消费的**共享脚手架**,
// 却住在 ProductionEnvironmentTests.cs —— 一个以某个测试类命名的文件里。
// 按文件名找不到它们,而它们的消费面比那个测试类大一个量级。
// 纯搬迁:类型、可见性、成员逐字不变;本文件不含任何测试方法(见下方判据)。

internal sealed class FakeRepositoryGateway(
    RawChangeSet changes,
    RawRepositorySnapshot? current,
    RawRepositorySnapshot? baseline,
    Func<FrozenRevisionIdentity>? currentRevisionResolver = null,
    Func<string, RawChangeSet>? changesForBase = null,
    Func<RawRepositorySnapshot>? currentReader = null)
    : IRepositoryGateway
{
    internal int ReadCount { get; private set; }

    internal int ReadCurrentCount { get; private set; }

    internal List<string> ReadRevisionCalls { get; } = [];

    internal List<string> ReadChangesCalls { get; } = [];

    internal int CurrentRevisionResolutionCount { get; private set; }

    public AdmissionTopologyOutcome InspectAdmissionTopology() =>
        throw new InvalidOperationException("topology should not be inspected");

    public PreparedRepository Prepare(string? protectedBase) => new("baseline", changes);

    public FrozenRevisionIdentity ResolveFrozenRevision(string revision)
    {
        var algorithm = revision.Length == 40 ? "git-sha1:" : "git-sha256:";
        return new FrozenRevisionIdentity(
            revision,
            algorithm + revision,
            algorithm + new string('b', revision.Length));
    }

    public FrozenRevisionIdentity ResolveCurrentRevision()
    {
        CurrentRevisionResolutionCount++;
        return currentRevisionResolver?.Invoke()
            ?? ResolveFrozenRevision(new string('a', 40));
    }

    public RawRepositorySnapshot ReadCurrent()
    {
        ReadCount++;
        ReadCurrentCount++;
        return WithAtomizerData(
            currentReader?.Invoke()
            ?? current
            ?? throw new InvalidOperationException("current snapshot should not be read"));
    }

    public RawRepositorySnapshot ReadRevision(string revision)
    {
        ReadCount++;
        ReadRevisionCalls.Add(revision);
        return WithAtomizerData(
            baseline ?? throw new InvalidOperationException("baseline snapshot should not be read"));
    }

    public RawChangeSet ReadCurrentChanges() => changes;

    public RawChangeSet ReadChanges(string revision)
    {
        ReadChangesCalls.Add(revision);
        return changesForBase?.Invoke(revision) ?? changes;
    }

    private static RawRepositorySnapshot WithAtomizerData(RawRepositorySnapshot snapshot) =>
        snapshot.Entries.Any(static entry => entry.Path == TheoryAtomizerDataLoader.DataPath)
            ? snapshot
            : RawRepositorySnapshot.Create(snapshot.Entries.Add(new RawRepositoryEntry(
                TheoryAtomizerDataLoader.DataPath,
                ImmutableArray.CreateRange(DigestionTestSupport.RulesBytes))));
}

internal sealed class FakeLeanReportSource(LeanAxiomReport? report) : ILeanReportSource
{
    internal int CallCount { get; private set; }

    public LeanAxiomReport Load(RepositorySnapshot snapshot)
    {
        CallCount++;
        return report ?? throw new InvalidOperationException("Lean report source should not be called");
    }
}

internal sealed class FakeScribeEmissionVerifier(VerifiedScribeEmissions? verification)
    : IScribeEmissionVerifier
{
    internal int CallCount { get; private set; }

    public VerifiedScribeEmissions Verify(
        RepositorySnapshot snapshot,
        LeanAxiomReport report,
        RawChangeSet? changes = null)
    {
        CallCount++;
        return verification
            ?? throw new InvalidOperationException("Scribe emission verification failed: synthetic");
    }
}
