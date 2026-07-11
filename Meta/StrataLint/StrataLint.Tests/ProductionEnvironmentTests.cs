using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ProductionEnvironmentTests
{
    [Fact]
    public void CheckShortCircuitsAtSl022BeforeCandidateContentOrLeanIsRead()
    {
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create(new[] { "Meta/StrataLint/StrataLint.Engine/Gid.cs" }),
            current: null,
            baseline: null);
        var inspector = new FakeLeanInspector(null);
        var environment = new ProductionCliEnvironment("/repo", gateway, inspector);

        var outcome = environment.Check(Array.Empty<string>());

        var required = Assert.IsType<AdmissionOutcome.HumanReviewRequired>(outcome);
        Assert.Contains(required.Diagnostics, item => item.RuleId == RuleId.CreateKnown(22));
        Assert.Equal(0, gateway.ReadCount);
        Assert.Equal(0, inspector.CallCount);
    }

    [Fact]
    public void CheckRunsTheCompleteCapabilityChainForOrdinaryChanges()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files["Meta/registry.yaml"] = TestRegistry.Canonical;
        fixture.Baseline["Meta/registry.yaml"] = TestRegistry.Canonical;
        fixture.Files["Meta/domains.yaml"] = TestRegistry.Domains;
        fixture.Baseline["Meta/domains.yaml"] = TestRegistry.Domains;
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create(new[] { RuleFixture.BlueprintPath }),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline));
        var inspector = new FakeLeanInspector(LeanAxiomReport.Create(fixture.Reports));
        var environment = new ProductionCliEnvironment("/repo", gateway, inspector);

        var outcome = environment.Check(Array.Empty<string>());

        Assert.IsType<AdmissionOutcome.Admitted>(outcome);
        Assert.Equal(2, gateway.ReadCount);
        Assert.Equal(2, inspector.CallCount);
    }

    [Fact]
    public void RouteUsesTheRepositoryRegistryAndEmitsStableJson()
    {
        using var temporary = new TemporaryDirectory();
        Directory.CreateDirectory(Path.Combine(temporary.Path, "Meta"));
        File.WriteAllText(Path.Combine(temporary.Path, "Meta", "registry.yaml"), TestRegistry.Canonical, new UTF8Encoding(false));
        File.WriteAllText(Path.Combine(temporary.Path, "Meta", "domains.yaml"), TestRegistry.Domains, new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(temporary.Path, "manifest.json"),
            "{\"artifact\":\"lean\",\"domain\":\"Carrier\",\"generality\":\"G\",\"module\":\"Probe\",\"plane\":\"F\",\"selector\":\"\",\"tag\":\"\",\"theory\":\"D5\"}\n",
            new UTF8Encoding(false));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create(Array.Empty<string>()), null, null),
            new FakeLeanInspector(null));

        var result = environment.Route(new[] { "manifest.json" });

        Assert.True(result.Success, result.Error);
        Assert.Contains("\"gid\": \"D5/S0/Carrier/Probe\"", result.Output, StringComparison.Ordinal);
        Assert.EndsWith("\n", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void SelfTestIsByteStableAcrossTwoPasses()
    {
        using var temporary = new TemporaryDirectory();
        Directory.CreateDirectory(Path.Combine(temporary.Path, "Meta"));
        File.WriteAllText(Path.Combine(temporary.Path, "Meta", "registry.yaml"), TestRegistry.Canonical, new UTF8Encoding(false));
        File.WriteAllText(Path.Combine(temporary.Path, "Meta", "domains.yaml"), TestRegistry.Domains, new UTF8Encoding(false));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create(Array.Empty<string>()), null, null),
            new FakeLeanInspector(null));

        var first = environment.SelfTest(Array.Empty<string>());
        var second = environment.SelfTest(Array.Empty<string>());

        Assert.True(first.Success, first.Error);
        Assert.True(second.Success, second.Error);
        Assert.Equal(first.Output, second.Output);
        Assert.Contains("SELFTEST PASS", first.Output, StringComparison.Ordinal);
    }

    private static RawRepositorySnapshot Snapshot(IReadOnlyDictionary<string, string> files) =>
        RawRepositorySnapshot.Create(files.Select(pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
}

internal sealed class FakeRepositoryGateway(
    RawChangeSet changes,
    RawRepositorySnapshot? current,
    RawRepositorySnapshot? baseline) : IRepositoryGateway
{
    internal int ReadCount { get; private set; }

    public AdmissionTopologyOutcome InspectAdmissionTopology() =>
        throw new InvalidOperationException("topology should not be inspected");

    public PreparedRepository Prepare(string? protectedBase) => new("baseline", changes);

    public RawRepositorySnapshot ReadCurrent()
    {
        ReadCount++;
        return current ?? throw new InvalidOperationException("current snapshot should not be read");
    }

    public RawRepositorySnapshot ReadRevision(string revision)
    {
        ReadCount++;
        return baseline ?? throw new InvalidOperationException("baseline snapshot should not be read");
    }
}

internal sealed class FakeLeanInspector(LeanAxiomReport? report) : ILeanInspector
{
    internal int CallCount { get; private set; }

    public LeanAxiomReport Inspect(RepositorySnapshot snapshot)
    {
        CallCount++;
        return report ?? throw new InvalidOperationException("Lean inspector should not be called");
    }
}

internal sealed class TemporaryDirectory : IDisposable
{
    internal TemporaryDirectory()
    {
        Path = System.IO.Path.Combine(System.IO.Path.GetTempPath(), "stratalint-tests-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(Path);
    }

    internal string Path { get; }

    public void Dispose() => Directory.Delete(Path, recursive: true);
}
