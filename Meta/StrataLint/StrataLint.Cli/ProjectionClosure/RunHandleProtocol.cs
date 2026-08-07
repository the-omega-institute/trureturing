using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Scribe;

namespace StrataLint.Cli;

internal sealed record ArtifactInventoryItem(string ArtifactId, string Path, string Mode);

internal sealed record ArtifactInventory(ImmutableArray<ArtifactInventoryItem> Artifacts);

internal sealed record RunRequest(
    string RunId,
    string SourceTreeSha256,
    string BaseTreeSha256,
    string ProducerBuildSha256,
    long SourceDateEpoch,
    string ExpectedArtifactInventorySha256);

internal sealed record RunArtifact(string ArtifactId, string Path, string Sha256, string Mode);

internal sealed record RunVerifier(string Id, string ResultSha256, string Disposition);

internal sealed record RunReceipt(
    string RequestSha256,
    string RunId,
    string SourceTreeSha256,
    string BaseTreeSha256,
    string ProducerBuildSha256,
    long SourceDateEpoch,
    ImmutableArray<RunArtifact> Artifacts,
    string ArtifactSetSha256,
    string CrossArtifactSha256,
    ImmutableArray<RunVerifier> Verifiers,
    bool Pass);

internal sealed record RunHandle(string RequestSha256, string RunId, string ReceiptPath, string ReceiptSha256);

internal sealed record RunHandleResult(int ExitCode, string Error = "");

internal static class RunHandleInventory
{
    internal static ArtifactInventory Load(string repositoryRoot)
    {
        var artifacts = FileMapLoader.LoadRepository(repositoryRoot).Entries
            .Where(static entry => entry.RuntimeDisposition == "run-local")
            .Select(static entry => new ArtifactInventoryItem(entry.ArtifactId!, entry.Pattern, entry.Mode!))
            .OrderBy(static item => item.Path, StringComparer.Ordinal)
            .ThenBy(static item => item.ArtifactId, StringComparer.Ordinal)
            .ToImmutableArray();
        if (artifacts.IsEmpty) throw new InvalidOperationException("FILEMAP has no run-local artifacts");
        return new ArtifactInventory(artifacts);
    }
}

internal static class RunHandleCanonicalWriter
{
    internal static byte[] WriteRequest(RunRequest request) => Write(writer =>
    {
        writer.WriteStartObject();
        writer.WriteString("base_tree_sha256", request.BaseTreeSha256);
        writer.WriteString("expected_artifact_inventory_sha256", request.ExpectedArtifactInventorySha256);
        writer.WriteString("producer_build_sha256", request.ProducerBuildSha256);
        writer.WriteString("run_id", request.RunId);
        writer.WriteString("schema", "run-request-v1");
        writer.WriteNumber("source_date_epoch", request.SourceDateEpoch);
        writer.WriteString("source_tree_sha256", request.SourceTreeSha256);
        writer.WriteEndObject();
    });

    internal static byte[] WriteInventory(ArtifactInventory inventory) => Write(writer =>
    {
        writer.WriteStartObject();
        writer.WritePropertyName("artifacts");
        writer.WriteStartArray();
        foreach (var artifact in inventory.Artifacts)
        {
            writer.WriteStartObject();
            writer.WriteString("artifact_id", artifact.ArtifactId);
            writer.WriteString("mode", artifact.Mode);
            writer.WriteString("path", artifact.Path);
            writer.WriteEndObject();
        }
        writer.WriteEndArray();
        writer.WriteString("schema", "artifact-inventory-v1");
        writer.WriteEndObject();
    });

    internal static byte[] WriteArtifacts(ImmutableArray<RunArtifact> artifacts) => Write(writer =>
    {
        writer.WriteStartArray();
        WriteArtifactsValue(writer, artifacts);
        writer.WriteEndArray();
    });

    internal static byte[] WriteReceipt(RunReceipt receipt) => Write(writer =>
    {
        writer.WriteStartObject();
        writer.WriteString("artifact_set_sha256", receipt.ArtifactSetSha256);
        writer.WritePropertyName("artifacts");
        writer.WriteStartArray();
        WriteArtifactsValue(writer, receipt.Artifacts);
        writer.WriteEndArray();
        writer.WriteString("base_tree_sha256", receipt.BaseTreeSha256);
        writer.WriteString("cross_artifact_sha256", receipt.CrossArtifactSha256);
        writer.WriteBoolean("pass", receipt.Pass);
        writer.WriteString("producer_build_sha256", receipt.ProducerBuildSha256);
        writer.WriteString("request_sha256", receipt.RequestSha256);
        writer.WriteString("run_id", receipt.RunId);
        writer.WriteString("schema", "receipt-v1");
        writer.WriteNumber("source_date_epoch", receipt.SourceDateEpoch);
        writer.WriteString("source_tree_sha256", receipt.SourceTreeSha256);
        writer.WritePropertyName("verifiers");
        writer.WriteStartArray();
        WriteVerifiersValue(writer, receipt.Verifiers);
        writer.WriteEndArray();
        writer.WriteEndObject();
    });

    internal static byte[] WriteHandle(RunHandle handle) => Write(writer =>
    {
        writer.WriteStartObject();
        writer.WriteString("receipt_path", handle.ReceiptPath);
        writer.WriteString("receipt_sha256", handle.ReceiptSha256);
        writer.WriteString("request_sha256", handle.RequestSha256);
        writer.WriteString("run_id", handle.RunId);
        writer.WriteString("schema", "run-handle-v1");
        writer.WriteEndObject();
    });

    internal static byte[] WriteCrossArtifact(RunReceipt receipt) => Write(writer =>
    {
        writer.WriteStartObject();
        writer.WriteString("artifact_set_sha256", receipt.ArtifactSetSha256);
        writer.WriteString("base_tree_sha256", receipt.BaseTreeSha256);
        writer.WriteString("producer_build_sha256", receipt.ProducerBuildSha256);
        writer.WriteString("request_sha256", receipt.RequestSha256);
        writer.WriteString("source_tree_sha256", receipt.SourceTreeSha256);
        writer.WritePropertyName("verifiers");
        writer.WriteStartArray();
        WriteVerifiersValue(writer, receipt.Verifiers);
        writer.WriteEndArray();
        writer.WriteEndObject();
    });

    private static void WriteArtifactsValue(Utf8JsonWriter writer, IEnumerable<RunArtifact> artifacts)
    {
        foreach (var artifact in artifacts)
        {
            writer.WriteStartObject();
            writer.WriteString("artifact_id", artifact.ArtifactId);
            writer.WriteString("mode", artifact.Mode);
            writer.WriteString("path", artifact.Path);
            writer.WriteString("sha256", artifact.Sha256);
            writer.WriteEndObject();
        }
    }

    private static void WriteVerifiersValue(Utf8JsonWriter writer, IEnumerable<RunVerifier> verifiers)
    {
        foreach (var verifier in verifiers)
        {
            writer.WriteStartObject();
            writer.WriteString("disposition", verifier.Disposition);
            writer.WriteString("id", verifier.Id);
            writer.WriteString("result_sha256", verifier.ResultSha256);
            writer.WriteEndObject();
        }
    }

    private static byte[] Write(Action<Utf8JsonWriter> action)
    {
        using var stream = new MemoryStream();
        using (var writer = new Utf8JsonWriter(stream, new JsonWriterOptions { Indented = false }))
        {
            action(writer);
        }
        return stream.ToArray();
    }
}

internal static class RunHandleDigests
{
    internal static string Request(RunRequest request) => Sha(RunHandleCanonicalWriter.WriteRequest(request));
    internal static string Inventory(ArtifactInventory inventory) => Domain("artifact-inventory-v1", RunHandleCanonicalWriter.WriteInventory(inventory));
    internal static string ArtifactSet(ImmutableArray<RunArtifact> artifacts) => Domain("artifact-set-v1", RunHandleCanonicalWriter.WriteArtifacts(artifacts));
    internal static string CrossArtifact(RunReceipt receipt) => Sha(RunHandleCanonicalWriter.WriteCrossArtifact(receipt));
    internal static string Sha(ReadOnlySpan<byte> bytes) => Convert.ToHexStringLower(SHA256.HashData(bytes));

    private static string Domain(string domain, byte[] bytes)
    {
        var prefix = Encoding.UTF8.GetBytes(domain + "\0");
        return Sha(prefix.Concat(bytes).ToArray());
    }
}

internal static class RunHandlePublisher
{
    internal static RunHandleResult Publish(
        string outputRoot,
        RunRequest request,
        ArtifactInventory inventory,
        IReadOnlyDictionary<string, byte[]> artifactBytes,
        ImmutableArray<RunVerifier> verifiers,
        string? failurePoint = null)
    {
        string? staging = null;
        string? final = null;
        string? handleTemp = null;
        string? handlePath = null;
        try
        {
            ValidateRoot(outputRoot);
            ValidateRequest(request, inventory);
            final = Path.Combine(outputRoot, request.RunId);
            staging = Path.Combine(outputRoot, $".{request.RunId}.tmp");
            handleTemp = Path.Combine(outputRoot, $".{request.RunId}.handle.tmp");
            handlePath = Path.Combine(outputRoot, $"{request.RunId}.handle.json");
            if (Directory.Exists(final) || Directory.Exists(staging) || File.Exists(handlePath) || File.Exists(handleTemp))
            {
                throw new InvalidOperationException("run_id already exists");
            }
            Directory.CreateDirectory(staging);
            var runArtifacts = inventory.Artifacts.Select(item =>
            {
                if (!artifactBytes.TryGetValue(item.Path, out var bytes))
                {
                    throw new InvalidOperationException($"missing artifact bytes: {item.Path}");
                }
                var target = ResolveContained(staging, item.Path, requireExisting: false);
                Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                WriteDurable(target, bytes);
                if (!OperatingSystem.IsWindows()) File.SetUnixFileMode(target, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.GroupRead | UnixFileMode.OtherRead);
                return new RunArtifact(item.ArtifactId, item.Path, RunHandleDigests.Sha(bytes), item.Mode);
            }).ToImmutableArray();
            Inject(failurePoint, "after-artifacts");
            var requestSha = RunHandleDigests.Request(request);
            var artifactSetSha = RunHandleDigests.ArtifactSet(runArtifacts);
            var receipt = new RunReceipt(requestSha, request.RunId, request.SourceTreeSha256,
                request.BaseTreeSha256, request.ProducerBuildSha256, request.SourceDateEpoch,
                runArtifacts, artifactSetSha, string.Empty, verifiers, true);
            receipt = receipt with { CrossArtifactSha256 = RunHandleDigests.CrossArtifact(receipt) };
            var receiptBytes = RunHandleCanonicalWriter.WriteReceipt(receipt);
            WriteDurable(Path.Combine(staging, "receipt.json"), receiptBytes);
            Inject(failurePoint, "after-receipt");
            Directory.Move(staging, final);
            staging = null;
            Inject(failurePoint, "after-run-rename");
            var handle = new RunHandle(requestSha, request.RunId, "receipt.json", RunHandleDigests.Sha(receiptBytes));
            WriteDurable(handleTemp, RunHandleCanonicalWriter.WriteHandle(handle));
            Inject(failurePoint, "before-handle-rename");
            File.Move(handleTemp, handlePath);
            handleTemp = null;
            return new RunHandleResult(0);
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException
            or ArgumentException or InvalidOperationException or JsonException)
        {
            if (handleTemp is not null && File.Exists(handleTemp)) File.Delete(handleTemp);
            if (handlePath is not null && File.Exists(handlePath)) File.Delete(handlePath);
            if (staging is not null && Directory.Exists(staging)) Directory.Delete(staging, recursive: true);
            if (final is not null && Directory.Exists(final)) Directory.Delete(final, recursive: true);
            return new RunHandleResult(1, exception.Message);
        }
    }

    internal static string ResolveContained(string root, string relativePath, bool requireExisting)
    {
        if (string.IsNullOrEmpty(relativePath) || Path.IsPathRooted(relativePath)
            || relativePath.Contains('\\') || relativePath.Split('/').Any(static part => part is "" or "." or "..")
            || !relativePath.IsNormalized(NormalizationForm.FormC))
        {
            throw new InvalidOperationException("artifact path is not canonical");
        }
        var rootFull = Path.GetFullPath(root) + Path.DirectorySeparatorChar;
        var full = Path.GetFullPath(Path.Combine(root, relativePath));
        if (!full.StartsWith(rootFull, StringComparison.Ordinal)) throw new InvalidOperationException("artifact path escapes run");
        var current = root;
        foreach (var part in relativePath.Split('/'))
        {
            current = Path.Combine(current, part);
            if ((File.Exists(current) || Directory.Exists(current)) && File.GetAttributes(current).HasFlag(FileAttributes.ReparsePoint))
                throw new InvalidOperationException("artifact path traverses symlink");
        }
        if (requireExisting && !File.Exists(full)) throw new InvalidOperationException("artifact is missing");
        return full;
    }

    private static void ValidateRoot(string outputRoot)
    {
        if (string.IsNullOrWhiteSpace(outputRoot) || !Path.IsPathFullyQualified(outputRoot)
            || !Directory.Exists(outputRoot) || File.GetAttributes(outputRoot).HasFlag(FileAttributes.ReparsePoint)
            || Directory.EnumerateFileSystemEntries(outputRoot).Any())
            throw new InvalidOperationException("output root must be absolute, existing, empty, and not a symlink");
    }

    private static void ValidateRequest(RunRequest request, ArtifactInventory inventory)
    {
        if (request.RunId.Length != 32 || request.RunId.Any(static c => c is not (>= '0' and <= '9' or >= 'a' and <= 'f'))
            || request.SourceDateEpoch < 0 || !ProjectionClosureValidator.IsSha256(request.SourceTreeSha256)
            || !ProjectionClosureValidator.IsSha256(request.BaseTreeSha256)
            || !ProjectionClosureValidator.IsSha256(request.ProducerBuildSha256)
            || request.ExpectedArtifactInventorySha256 != RunHandleDigests.Inventory(inventory))
            throw new InvalidOperationException("request is invalid");
        var sorted = inventory.Artifacts.OrderBy(static item => item.Path, StringComparer.Ordinal)
            .ThenBy(static item => item.ArtifactId, StringComparer.Ordinal).ToImmutableArray();
        if (!inventory.Artifacts.SequenceEqual(sorted) || inventory.Artifacts.Distinct().Count() != inventory.Artifacts.Length
            || inventory.Artifacts.Any(static item => item.Mode is not ("100644" or "100755")))
            throw new InvalidOperationException("inventory is invalid");
    }

    private static void WriteDurable(string path, byte[] bytes)
    {
        using var stream = new FileStream(path, FileMode.CreateNew, FileAccess.Write, FileShare.None);
        stream.Write(bytes);
        stream.Flush(flushToDisk: true);
    }

    private static void Inject(string? actual, string expected)
    {
        if (actual == expected) throw new IOException("injected failure: " + expected);
    }
}

internal static class RunHandleConsumer
{
    internal static RunHandleResult Verify(string outputRoot, string runId, string expectedRequestSha256, ArtifactInventory inventory)
    {
        try
        {
            if (!ProjectionClosureValidator.IsSha256(expectedRequestSha256)) throw new InvalidOperationException("expected request digest invalid");
            var handlePath = Path.Combine(outputRoot, $"{runId}.handle.json");
            using var handleDocument = JsonDocument.Parse(File.ReadAllBytes(handlePath));
            RequireFields(handleDocument.RootElement, "receipt_path", "receipt_sha256", "request_sha256", "run_id", "schema");
            var handle = handleDocument.RootElement;
            if (handle.GetProperty("schema").GetString() != "run-handle-v1"
                || handle.GetProperty("run_id").GetString() != runId
                || handle.GetProperty("request_sha256").GetString() != expectedRequestSha256
                || handle.GetProperty("receipt_path").GetString() != "receipt.json")
                throw new InvalidOperationException("handle binding mismatch");
            var parsedHandle = new RunHandle(expectedRequestSha256, runId, "receipt.json", handle.GetProperty("receipt_sha256").GetString()!);
            if (!File.ReadAllBytes(handlePath).AsSpan().SequenceEqual(RunHandleCanonicalWriter.WriteHandle(parsedHandle)))
                throw new InvalidOperationException("handle bytes are not canonical");
            var runRoot = Path.Combine(outputRoot, runId);
            var receiptPath = RunHandlePublisher.ResolveContained(runRoot, "receipt.json", requireExisting: true);
            var receiptBytes = File.ReadAllBytes(receiptPath);
            if (RunHandleDigests.Sha(receiptBytes) != handle.GetProperty("receipt_sha256").GetString())
                throw new InvalidOperationException("receipt digest mismatch");
            using var receiptDocument = JsonDocument.Parse(receiptBytes);
            RequireFields(receiptDocument.RootElement, "artifact_set_sha256", "artifacts", "base_tree_sha256",
                "cross_artifact_sha256", "pass", "producer_build_sha256", "request_sha256", "run_id", "schema",
                "source_date_epoch", "source_tree_sha256", "verifiers");
            var receipt = receiptDocument.RootElement;
            if (receipt.GetProperty("schema").GetString() != "receipt-v1"
                || receipt.GetProperty("request_sha256").GetString() != expectedRequestSha256
                || receipt.GetProperty("run_id").GetString() != runId
                || receipt.GetProperty("pass").ValueKind != JsonValueKind.True)
                throw new InvalidOperationException("receipt binding mismatch");
            var reconstructedRequest = new RunRequest(runId, receipt.GetProperty("source_tree_sha256").GetString()!,
                receipt.GetProperty("base_tree_sha256").GetString()!, receipt.GetProperty("producer_build_sha256").GetString()!,
                receipt.GetProperty("source_date_epoch").GetInt64(), RunHandleDigests.Inventory(inventory));
            if (RunHandleDigests.Request(reconstructedRequest) != expectedRequestSha256)
                throw new InvalidOperationException("request digest does not match receipt and pinned inventory");
            var actual = receipt.GetProperty("artifacts").EnumerateArray().Select(item =>
            {
                RequireFields(item, "artifact_id", "mode", "path", "sha256");
                return new RunArtifact(item.GetProperty("artifact_id").GetString()!, item.GetProperty("path").GetString()!,
                    item.GetProperty("sha256").GetString()!, item.GetProperty("mode").GetString()!);
            }).ToImmutableArray();
            var projected = actual.Select(static item => new ArtifactInventoryItem(item.ArtifactId, item.Path, item.Mode)).ToImmutableArray();
            if (!projected.SequenceEqual(inventory.Artifacts)) throw new InvalidOperationException("inventory projection mismatch");
            foreach (var artifact in actual)
            {
                var path = RunHandlePublisher.ResolveContained(runRoot, artifact.Path, requireExisting: true);
                if (RunHandleDigests.Sha(File.ReadAllBytes(path)) != artifact.Sha256) throw new InvalidOperationException("artifact digest mismatch");
                if (!OperatingSystem.IsWindows() && artifact.Mode == "100644"
                    && (File.GetUnixFileMode(path) & (UnixFileMode.UserExecute | UnixFileMode.GroupExecute | UnixFileMode.OtherExecute)) != 0)
                    throw new InvalidOperationException("artifact mode mismatch");
            }
            if (RunHandleDigests.ArtifactSet(actual) != receipt.GetProperty("artifact_set_sha256").GetString())
                throw new InvalidOperationException("artifact set digest mismatch");
            var verifiers = receipt.GetProperty("verifiers").EnumerateArray().Select(item =>
            {
                RequireFields(item, "disposition", "id", "result_sha256");
                return new RunVerifier(item.GetProperty("id").GetString()!, item.GetProperty("result_sha256").GetString()!,
                    item.GetProperty("disposition").GetString()!);
            }).ToImmutableArray();
            var parsedReceipt = new RunReceipt(expectedRequestSha256, runId, reconstructedRequest.SourceTreeSha256,
                reconstructedRequest.BaseTreeSha256, reconstructedRequest.ProducerBuildSha256, reconstructedRequest.SourceDateEpoch,
                actual, receipt.GetProperty("artifact_set_sha256").GetString()!,
                receipt.GetProperty("cross_artifact_sha256").GetString()!, verifiers, true);
            if (RunHandleDigests.CrossArtifact(parsedReceipt) != parsedReceipt.CrossArtifactSha256)
                throw new InvalidOperationException("cross artifact digest mismatch");
            if (!receiptBytes.AsSpan().SequenceEqual(RunHandleCanonicalWriter.WriteReceipt(parsedReceipt)))
                throw new InvalidOperationException("receipt bytes are not canonical");
            return new RunHandleResult(0);
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException
            or ArgumentException or InvalidOperationException or JsonException)
        {
            return new RunHandleResult(1, exception.Message);
        }
    }

    private static void RequireFields(JsonElement element, params string[] expected)
    {
        var actual = element.EnumerateObject().Select(static property => property.Name).ToArray();
        if (!actual.SequenceEqual(expected)) throw new InvalidOperationException("schema is not closed or canonical");
    }
}

internal static class RunHandleCommand
{
    internal static ExplicitCommandResult Run(string repositoryRoot, IReadOnlyList<string> arguments)
    {
        try
        {
            var inventory = RunHandleInventory.Load(repositoryRoot);
            if (arguments.Count == 5 && arguments[0] == "publish" && arguments[1] == "--request"
                && arguments[3] == "--output-root")
            {
                var request = ParseRequest(File.ReadAllBytes(Resolve(repositoryRoot, arguments[2])));
                var bytes = inventory.Artifacts.ToImmutableDictionary(
                    static item => item.Path,
                    item => File.ReadAllBytes(Path.Combine(repositoryRoot, item.Path)),
                    StringComparer.Ordinal);
                var result = RunHandlePublisher.Publish(arguments[4], request, inventory, bytes, []);
                return new ExplicitCommandResult(result.ExitCode, result.ExitCode == 0 ? "published run-handle-v1\n" : string.Empty,
                    result.ExitCode == 0 ? string.Empty : result.Error + "\n");
            }
            if (arguments.Count == 7 && arguments[0] == "verify" && arguments[1] == "--output-root"
                && arguments[3] == "--run-id" && arguments[5] == "--expected-request-sha256")
            {
                var result = RunHandleConsumer.Verify(arguments[2], arguments[4], arguments[6], inventory);
                return new ExplicitCommandResult(result.ExitCode, result.ExitCode == 0 ? "verified run-handle-v1\n" : string.Empty,
                    result.ExitCode == 0 ? string.Empty : result.Error + "\n");
            }
            return Usage();
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException
            or ArgumentException or InvalidOperationException or JsonException or FormatException)
        {
            return new ExplicitCommandResult(1, string.Empty, exception.Message + "\n");
        }
    }

    private static RunRequest ParseRequest(byte[] bytes)
    {
        using var document = JsonDocument.Parse(bytes);
        var root = document.RootElement;
        var fields = root.EnumerateObject().Select(static property => property.Name).ToArray();
        var expected = new[] { "base_tree_sha256", "expected_artifact_inventory_sha256", "producer_build_sha256",
            "run_id", "schema", "source_date_epoch", "source_tree_sha256" };
        if (!fields.SequenceEqual(expected) || root.GetProperty("schema").GetString() != "run-request-v1")
            throw new FormatException("request schema is not closed or canonical");
        var request = new RunRequest(root.GetProperty("run_id").GetString()!,
            root.GetProperty("source_tree_sha256").GetString()!, root.GetProperty("base_tree_sha256").GetString()!,
            root.GetProperty("producer_build_sha256").GetString()!, root.GetProperty("source_date_epoch").GetInt64(),
            root.GetProperty("expected_artifact_inventory_sha256").GetString()!);
        if (!bytes.AsSpan().SequenceEqual(RunHandleCanonicalWriter.WriteRequest(request)))
            throw new FormatException("request bytes are not RFC 8785 canonical");
        return request;
    }

    private static string Resolve(string root, string path) => Path.IsPathFullyQualified(path) ? path : Path.Combine(root, path);

    private static ExplicitCommandResult Usage() => new(2, string.Empty,
        "usage: projection-run publish --request FILE --output-root DIR | projection-run verify --output-root DIR --run-id ID --expected-request-sha256 SHA\n");
}

internal sealed record QuotientDisposition(string OldRaw, string OldCanonical, string New, string Classification, bool Pass);

internal static class ProjectionQuotientVerifier
{
    internal static bool Verify(QuotientDisposition receipt) =>
        receipt.Classification != "projection-staleness-only"
        || receipt.OldRaw == "reject" && receipt.OldCanonical == "admit"
            && receipt.New == "admit" && receipt.Pass;
}
