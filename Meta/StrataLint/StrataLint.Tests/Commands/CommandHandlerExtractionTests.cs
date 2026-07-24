using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CommandHandlerExtractionTests
{
    [Fact]
    public void CheckCommandRequiresBothPrecomputedLeanReports()
    {
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create(Array.Empty<string>()),
            current: null,
            baseline: null);

        var outcome = CheckCommand.Run(
            gateway,
            scribeEmissionVerifier: null,
            Array.Empty<string>());

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("--candidate-lean-report", failure.Message, StringComparison.Ordinal);
        Assert.Contains("--baseline-lean-report", failure.Message, StringComparison.Ordinal);
        Assert.Equal(0, gateway.ReadCount);
    }

    [Fact]
    public void RouteCommandUsesTheRepositoryRegistryAndEmitsStableJson()
    {
        using var temporary = new TemporaryDirectory();
        WriteRegistry(temporary.Path);
        File.WriteAllText(
            Path.Combine(temporary.Path, "manifest.json"),
            "{\"artifact\":\"lean\",\"domain\":\"Carrier\",\"generality\":\"G\","
            + "\"module\":\"Probe\",\"plane\":\"F\",\"selector\":\"\",\"tag\":\"\","
            + "\"theory\":\"D5\"}\n",
            new UTF8Encoding(false));

        var result = RouteCommand.Run(temporary.Path, ["manifest.json"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("\"gid\": \"D5/S0/Carrier/Probe\"", result.Output, StringComparison.Ordinal);
        Assert.EndsWith("\n", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void SelfTestCommandIsByteStableAcrossTwoPasses()
    {
        using var temporary = new TemporaryDirectory();
        WriteRegistry(temporary.Path);

        var first = SelfTestCommand.Run(temporary.Path, Array.Empty<string>());
        var second = SelfTestCommand.Run(temporary.Path, Array.Empty<string>());

        Assert.True(first.Success, first.Error);
        Assert.True(second.Success, second.Error);
        Assert.Equal(first.Output, second.Output);
        Assert.Contains("SELFTEST PASS", first.Output, StringComparison.Ordinal);
    }

    private static void WriteRegistry(string repositoryRoot)
    {
        var meta = Directory.CreateDirectory(Path.Combine(repositoryRoot, "Meta"));
        File.WriteAllText(
            Path.Combine(meta.FullName, "registry.yaml"),
            TestRegistry.Canonical,
            new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(meta.FullName, "domains.yaml"),
            TestRegistry.Domains,
            new UTF8Encoding(false));
    }
}
