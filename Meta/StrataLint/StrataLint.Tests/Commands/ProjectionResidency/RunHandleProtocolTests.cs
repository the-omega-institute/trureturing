using System.Text;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class RunHandleProtocolTests
{
    [Fact]
    public void ProducerAndConsumerRoundTripWithCallerSuppliedRequestDigest()
    {
        using var fixture = new RunFixture();

        var produced = RunHandleProducer.Produce(fixture.SourceRoot, fixture.OutputRoot, fixture.Request, fixture.Inventory);
        var consumed = RunHandleConsumer.Consume(fixture.OutputRoot, produced.RequestSha256, fixture.Inventory);

        Assert.True(produced.ExitCode == 0, produced.Diagnostic);
        Assert.Equal(0, consumed.ExitCode);
        Assert.True(File.Exists(Path.Combine(fixture.OutputRoot, "handle.json")));
    }

    [Fact]
    public void ConsumerRejectsCallerRequestMismatch()
    {
        using var fixture = new RunFixture();
        _ = RunHandleProducer.Produce(fixture.SourceRoot, fixture.OutputRoot, fixture.Request, fixture.Inventory);

        var result = RunHandleConsumer.Consume(fixture.OutputRoot, new string('f', 64), fixture.Inventory);

        Assert.Equal(1, result.ExitCode);
        Assert.Contains("RUN_HANDLE_REQUEST_MISMATCH", result.Diagnostic, StringComparison.Ordinal);
    }

    [Fact]
    public void ProducerRejectsNonEmptyOutputRootWithoutPublishingHandle()
    {
        using var fixture = new RunFixture();
        File.WriteAllText(Path.Combine(fixture.OutputRoot, "occupied"), "x");

        var result = RunHandleProducer.Produce(fixture.SourceRoot, fixture.OutputRoot, fixture.Request, fixture.Inventory);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("RUN_OUTPUT_ROOT_NOT_EMPTY", result.Diagnostic, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(fixture.OutputRoot, "handle.json")));
    }

    [Fact]
    public void ConsumerRejectsTraversalReceiptPath()
    {
        using var fixture = new RunFixture();
        var produced = RunHandleProducer.Produce(fixture.SourceRoot, fixture.OutputRoot, fixture.Request, fixture.Inventory);
        var handlePath = Path.Combine(fixture.OutputRoot, "handle.json");
        File.WriteAllText(handlePath, File.ReadAllText(handlePath).Replace("receipt.json", "../receipt.json", StringComparison.Ordinal));

        var result = RunHandleConsumer.Consume(fixture.OutputRoot, produced.RequestSha256, fixture.Inventory);

        Assert.Equal(1, result.ExitCode);
        Assert.Contains("RUN_HANDLE_INVALID", result.Diagnostic, StringComparison.Ordinal);
    }

    [Fact]
    public void ProducerFailureLeavesNoHandleOrFinalRunDirectory()
    {
        using var fixture = new RunFixture(includeMissingArtifact: true);

        var result = RunHandleProducer.Produce(fixture.SourceRoot, fixture.OutputRoot, fixture.Request, fixture.Inventory);

        Assert.Equal(1, result.ExitCode);
        Assert.Contains("RUN_PRODUCER_FAILURE", result.Diagnostic, StringComparison.Ordinal);
        Assert.Empty(Directory.EnumerateFileSystemEntries(fixture.OutputRoot));
    }

    [Fact]
    public void ConsumerRejectsArtifactSymlinkEscape()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new RunFixture();
        var produced = RunHandleProducer.Produce(fixture.SourceRoot, fixture.OutputRoot, fixture.Request, fixture.Inventory);
        var artifact = Path.Combine(fixture.OutputRoot, "00000000000000000000000000000000", "Generated", "output.txt");
        File.Delete(artifact);
        File.CreateSymbolicLink(artifact, "/etc/hosts");

        var result = RunHandleConsumer.Consume(fixture.OutputRoot, produced.RequestSha256, fixture.Inventory);

        Assert.Equal(1, result.ExitCode);
        Assert.Contains("symlink", result.Diagnostic, StringComparison.Ordinal);
    }

    [Fact]
    public void ConsumerRejectsArtifactBytesThatDisagreeWithReceipt()
    {
        using var fixture = new RunFixture();
        var produced = RunHandleProducer.Produce(
            fixture.SourceRoot, fixture.OutputRoot, fixture.Request, fixture.Inventory);
        var artifact = Path.Combine(
            fixture.OutputRoot,
            "00000000000000000000000000000000",
            "Generated",
            "output.txt");
        File.WriteAllText(artifact, "tampered\n");

        var result = RunHandleConsumer.Consume(
            fixture.OutputRoot, produced.RequestSha256, fixture.Inventory);

        Assert.Equal(1, result.ExitCode);
        Assert.Contains("RUN_HANDLE_INVALID artifact bytes mismatch", result.Diagnostic,
            StringComparison.Ordinal);
    }

    [Fact]
    public void ConsumerRejectsCrossRunHandle()
    {
        using var fixture = new RunFixture();
        var produced = RunHandleProducer.Produce(fixture.SourceRoot, fixture.OutputRoot, fixture.Request, fixture.Inventory);
        var handlePath = Path.Combine(fixture.OutputRoot, "handle.json");
        using var handle = System.Text.Json.JsonDocument.Parse(File.ReadAllBytes(handlePath));
        var replacement = RunHandleJson.Write(new Dictionary<string, object?>
        {
            ["schema"] = "run-handle-v1",
            ["request_sha256"] = handle.RootElement.GetProperty("request_sha256").GetString(),
            ["run_id"] = "11111111111111111111111111111111",
            ["receipt_path"] = "receipt.json",
            ["receipt_sha256"] = handle.RootElement.GetProperty("receipt_sha256").GetString(),
        });
        File.WriteAllBytes(handlePath, replacement);

        var result = RunHandleConsumer.Consume(fixture.OutputRoot, produced.RequestSha256, fixture.Inventory);

        Assert.Equal(1, result.ExitCode);
        Assert.Contains("no unique final directory", result.Diagnostic, StringComparison.Ordinal);
    }

    private sealed class RunFixture : IDisposable
    {
        private readonly string root = Path.Combine(Path.GetTempPath(), "run-handle-test-" + Guid.NewGuid().ToString("N"));

        internal RunFixture(bool includeMissingArtifact = false)
        {
            SourceRoot = Path.Combine(root, "source");
            OutputRoot = Path.Combine(root, "output");
            Directory.CreateDirectory(Path.Combine(SourceRoot, "Generated"));
            Directory.CreateDirectory(OutputRoot);
            File.WriteAllText(Path.Combine(SourceRoot, "Generated", "output.txt"), "stable\n", new UTF8Encoding(false));
            Inventory = includeMissingArtifact
                ? [new RunArtifactInventoryItem("A-OUTPUT", "Generated/output.txt", "100644"), new RunArtifactInventoryItem("A-Z-MISSING", "Generated/z-missing.txt", "100644")]
                : [new RunArtifactInventoryItem("A-OUTPUT", "Generated/output.txt", "100644")];
            var inventorySha = RunHandleDigests.Inventory(Inventory);
            Request = RunHandleJson.Write(new Dictionary<string, object?>
            {
                ["schema"] = "run-request-v1",
                ["run_id"] = "00000000000000000000000000000000",
                ["source_tree_sha256"] = new string('1', 64),
                ["base_tree_sha256"] = new string('2', 64),
                ["producer_build_sha256"] = new string('3', 64),
                ["source_date_epoch"] = 0,
                ["expected_artifact_inventory_sha256"] = inventorySha,
            });
        }

        internal string SourceRoot { get; }
        internal string OutputRoot { get; }
        internal byte[] Request { get; }
        internal IReadOnlyList<RunArtifactInventoryItem> Inventory { get; }

        public void Dispose() => Directory.Delete(root, recursive: true);
    }
}
