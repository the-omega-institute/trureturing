using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class RunHandleProtocolTests
{
    private static readonly string Sha = new('a', 64);

    [Fact]
    public void RequestIsClosedAndContainsNoArtifactByteDigest()
    {
        var request = Request();
        var bytes = RunHandleCanonicalWriter.WriteRequest(request);
        using var document = JsonDocument.Parse(bytes);
        Assert.Equal(new[]
        {
            "base_tree_sha256", "expected_artifact_inventory_sha256", "producer_build_sha256",
            "run_id", "schema", "source_date_epoch", "source_tree_sha256",
        }, document.RootElement.EnumerateObject().Select(static property => property.Name));
        Assert.DoesNotContain("artifact_set_sha256", Encoding.UTF8.GetString(bytes), StringComparison.Ordinal);
    }

    [Fact]
    public void InventoryDigestDependsOnlyOnIdentityPathAndMode()
    {
        var inventory = Inventory();
        Assert.Equal(RunHandleDigests.Inventory(inventory), RunHandleDigests.Inventory(inventory));
        Assert.NotEqual(
            RunHandleDigests.Inventory(inventory),
            RunHandleDigests.Inventory(inventory with
            {
                Artifacts = inventory.Artifacts.SetItem(0, inventory.Artifacts[0] with { Mode = "100755" }),
            }));
    }

    [Fact]
    public void AtomicPublishAndConsumerFailClosed()
    {
        using var temporary = new TemporaryDirectory();
        var outputRoot = Path.Combine(temporary.Path, "runs");
        Directory.CreateDirectory(outputRoot);
        var request = Request();
        var artifacts = ImmutableDictionary<string, byte[]>.Empty
            .Add("Generated/DAG.md", Encoding.UTF8.GetBytes("dag\n"))
            .Add("Generated/FILEMAP.md", Encoding.UTF8.GetBytes("filemap\n"));

        Assert.Equal(0, RunHandlePublisher.Publish(outputRoot, request, Inventory(), artifacts, []).ExitCode);
        Assert.Equal(1, RunHandleConsumer.Verify(
            outputRoot, request.RunId, new string('f', 64), Inventory()).ExitCode);
        Assert.Equal(0, RunHandleConsumer.Verify(
            outputRoot, request.RunId, RunHandleDigests.Request(request), Inventory()).ExitCode);
        Assert.Equal(1, RunHandlePublisher.Publish(outputRoot, request, Inventory(), artifacts, []).ExitCode);
    }

    [Fact]
    public void PublishRejectsInvalidRootsAndCleansInjectedFailures()
    {
        using var temporary = new TemporaryDirectory();
        var outputRoot = Path.Combine(temporary.Path, "runs");
        Directory.CreateDirectory(outputRoot);
        File.WriteAllText(Path.Combine(outputRoot, "occupied"), "x");
        Assert.Equal(1, RunHandlePublisher.Publish(
            outputRoot, Request(), Inventory(), ImmutableDictionary<string, byte[]>.Empty, []).ExitCode);

        var clean = Path.Combine(temporary.Path, "clean");
        Directory.CreateDirectory(clean);
        Assert.Equal(1, RunHandlePublisher.Publish(
            "relative", Request(), Inventory(), ImmutableDictionary<string, byte[]>.Empty, []).ExitCode);
        Assert.Equal(1, RunHandlePublisher.Publish(
            clean, Request(), Inventory(), ImmutableDictionary<string, byte[]>.Empty, [], "after-receipt").ExitCode);
        Assert.Empty(Directory.EnumerateFileSystemEntries(clean));
    }

    [Fact]
    public void SymlinkOutputRootIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var target = Path.Combine(temporary.Path, "target");
        var link = Path.Combine(temporary.Path, "link");
        Directory.CreateDirectory(target);
        Directory.CreateSymbolicLink(link, target);
        Assert.Equal(1, RunHandlePublisher.Publish(
            link, Request(), Inventory(), ImmutableDictionary<string, byte[]>.Empty, []).ExitCode);
    }

    [Fact]
    public void ProjectionStalenessOnlyRequiresNewAdmitAndMutationFails()
    {
        var receipt = new QuotientDisposition("reject", "admit", "admit", "projection-staleness-only", true);
        Assert.True(ProjectionQuotientVerifier.Verify(receipt));
        Assert.False(ProjectionQuotientVerifier.Verify(receipt with { New = "reject" }));
    }

    private static RunRequest Request() => new(
        "0123456789abcdef0123456789abcdef", Sha, Sha, Sha, 0, RunHandleDigests.Inventory(Inventory()));

    private static ArtifactInventory Inventory() => new(
        [
            new("A-DAG", "Generated/DAG.md", "100644"),
            new("A-FILEMAP", "Generated/FILEMAP.md", "100644"),
        ]);
}
