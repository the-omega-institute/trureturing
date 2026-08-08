using System.Collections.Immutable;
using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record RunArtifactInventoryItem(string ArtifactId, string Path, string Mode);
internal sealed record RunProtocolResult(int ExitCode, string Diagnostic, string RequestSha256 = "");

internal static class RunHandleDigests
{
    internal static string Inventory(IReadOnlyList<RunArtifactInventoryItem> inventory) =>
        Domain("artifact-inventory-v1", RunHandleJson.Write(new Dictionary<string, object?>
        {
            ["schema"] = "artifact-inventory-v1",
            ["artifacts"] = Ordered(inventory).Select(static item => new Dictionary<string, object?>
            {
                ["artifact_id"] = item.ArtifactId,
                ["path"] = item.Path,
                ["mode"] = item.Mode,
            }).ToArray(),
        }));

    internal static string Domain(string domain, ReadOnlySpan<byte> bytes)
    {
        var prefix = Encoding.UTF8.GetBytes(domain);
        var preimage = new byte[prefix.Length + 1 + bytes.Length];
        prefix.CopyTo(preimage, 0);
        bytes.CopyTo(preimage.AsSpan(prefix.Length + 1));
        return Convert.ToHexStringLower(SHA256.HashData(preimage));
    }

    internal static IEnumerable<RunArtifactInventoryItem> Ordered(IEnumerable<RunArtifactInventoryItem> items) =>
        items.OrderBy(static item => item.Path, StringComparer.Ordinal)
            .ThenBy(static item => item.ArtifactId, StringComparer.Ordinal);
}

internal static class RunHandleProducer
{
    internal static RunProtocolResult Produce(
        string sourceRoot,
        string outputRoot,
        ReadOnlySpan<byte> requestBytes,
        IReadOnlyList<RunArtifactInventoryItem> inventory)
    {
        string? staging = null;
        string? final = null;
        try
        {
            ValidateEmptyRoot(outputRoot);
            var request = RunRequest.Parse(requestBytes);
            var expectedInventory = RunHandleDigests.Inventory(inventory);
            if (request.ExpectedInventorySha256 != expectedInventory)
            {
                return new(1, "RUN_INVENTORY_MISMATCH expected inventory digest differs\n");
            }

            staging = Path.Combine(outputRoot, "." + request.RunId + ".tmp");
            final = Path.Combine(outputRoot, request.RunId);
            var handle = Path.Combine(outputRoot, "handle.json");
            var handleTemp = Path.Combine(outputRoot, ".handle.json.tmp");
            if (Directory.Exists(staging) || Directory.Exists(final) || File.Exists(handle) || File.Exists(handleTemp))
            {
                return new(1, "RUN_PUBLISH_COLLISION final, staging, handle, or handle temp already exists\n");
            }

            Directory.CreateDirectory(staging);
            var artifacts = new List<Dictionary<string, object?>>();
            foreach (var item in RunHandleDigests.Ordered(inventory))
            {
                RunPath.Validate(item.Path);
                var source = RunPath.ResolveContained(sourceRoot, item.Path, requireExists: true);
                var destination = RunPath.ResolveContained(staging, item.Path, requireExists: false);
                Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                var bytes = File.ReadAllBytes(source);
                WriteDurable(destination, bytes);
                artifacts.Add(new Dictionary<string, object?>
                {
                    ["artifact_id"] = item.ArtifactId,
                    ["path"] = item.Path,
                    ["sha256"] = Convert.ToHexStringLower(SHA256.HashData(bytes)),
                    ["mode"] = item.Mode,
                });
            }

            var requestSha = Convert.ToHexStringLower(SHA256.HashData(request.CanonicalBytes));
            var artifactSetSha = RunHandleDigests.Domain("artifact-set-v1", RunHandleJson.Write(artifacts));
            var verifierBytes = RunHandleJson.Write(new Dictionary<string, object?>
            {
                ["artifact_set_sha256"] = artifactSetSha,
                ["pass"] = true,
            });
            var verifiers = new[] { new Dictionary<string, object?>
            {
                ["id"] = "artifact-byte-verifier-v1",
                ["result_sha256"] = RunHandleDigests.Domain("artifact-byte-verifier-v1", verifierBytes),
                ["disposition"] = "pass",
            }};
            var cross = RunHandleJson.Write(new Dictionary<string, object?>
            {
                ["request_sha256"] = requestSha,
                ["source_tree_sha256"] = request.SourceTreeSha256,
                ["base_tree_sha256"] = request.BaseTreeSha256,
                ["producer_build_sha256"] = request.ProducerBuildSha256,
                ["artifact_set_sha256"] = artifactSetSha,
                ["verifiers"] = verifiers,
            });
            var receiptBytes = RunHandleJson.Write(new Dictionary<string, object?>
            {
                ["schema"] = "receipt-v1",
                ["request_sha256"] = requestSha,
                ["run_id"] = request.RunId,
                ["source_tree_sha256"] = request.SourceTreeSha256,
                ["base_tree_sha256"] = request.BaseTreeSha256,
                ["producer_build_sha256"] = request.ProducerBuildSha256,
                ["source_date_epoch"] = request.SourceDateEpoch,
                ["artifacts"] = artifacts,
                ["artifact_set_sha256"] = artifactSetSha,
                ["cross_artifact_sha256"] = Convert.ToHexStringLower(SHA256.HashData(cross)),
                ["verifiers"] = verifiers,
                ["pass"] = true,
            });
            WriteDurable(Path.Combine(staging, "receipt.json"), receiptBytes);
            RunDurability.SyncDirectoryTree(staging);
            Directory.Move(staging, final);
            staging = null;
            RunDurability.SyncDirectory(outputRoot);

            var handleBytes = RunHandleJson.Write(new Dictionary<string, object?>
            {
                ["schema"] = "run-handle-v1",
                ["request_sha256"] = requestSha,
                ["run_id"] = request.RunId,
                ["receipt_path"] = "receipt.json",
                ["receipt_sha256"] = RunHandleDigests.Domain("receipt-v1", receiptBytes),
            });
            WriteDurable(handleTemp, handleBytes);
            File.Move(handleTemp, handle);
            RunDurability.SyncDirectory(outputRoot);
            return new(0, "RUN_HANDLE_PUBLISHED\n", requestSha);
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException
            or FormatException or JsonException or CryptographicException)
        {
            if (staging is not null && Directory.Exists(staging)) Directory.Delete(staging, true);
            if (final is not null && Directory.Exists(final)) Directory.Delete(final, true);
            var handle = Path.Combine(outputRoot, "handle.json");
            var temp = Path.Combine(outputRoot, ".handle.json.tmp");
            if (File.Exists(handle)) File.Delete(handle);
            if (File.Exists(temp)) File.Delete(temp);
            return new(1, "RUN_PRODUCER_FAILURE " + exception.Message + "\n");
        }
    }

    private static void ValidateEmptyRoot(string outputRoot)
    {
        if (string.IsNullOrWhiteSpace(outputRoot) || !Path.IsPathFullyQualified(outputRoot))
            throw new FormatException("RUN_OUTPUT_ROOT_INVALID: output root must be non-empty and absolute");
        if (!Directory.Exists(outputRoot) || new DirectoryInfo(outputRoot).LinkTarget is not null)
            throw new FormatException("RUN_OUTPUT_ROOT_INVALID: output root must exist and not be a symlink");
        if (Directory.EnumerateFileSystemEntries(outputRoot).Any())
            throw new FormatException("RUN_OUTPUT_ROOT_NOT_EMPTY: output root must be empty");
    }

    private static void WriteDurable(string path, ReadOnlySpan<byte> bytes)
    {
        using var stream = new FileStream(path, FileMode.CreateNew, FileAccess.Write, FileShare.None);
        stream.Write(bytes);
        stream.Flush(flushToDisk: true);
    }
}

internal static class RunHandleConsumer
{
    internal static RunProtocolResult Consume(
        string outputRoot,
        string expectedRequestSha256,
        IReadOnlyList<RunArtifactInventoryItem> inventory)
    {
        try
        {
            RunRequest.RequireSha(expectedRequestSha256, "EXPECTED_REQUEST_SHA256");
            var handlePath = Path.Combine(outputRoot, "handle.json");
            if (!File.Exists(handlePath) || new FileInfo(handlePath).LinkTarget is not null)
                throw new FormatException("handle is missing or a symlink");
            var runDirectories = Directory.EnumerateDirectories(outputRoot)
                .Where(static path => !Path.GetFileName(path).StartsWith(".", StringComparison.Ordinal))
                .ToArray();
            if (runDirectories.Length != 1) throw new FormatException("expected exactly one run directory");
            using var handle = RunHandleJson.ParseCanonical(File.ReadAllBytes(handlePath));
            RunHandleJson.RequireFields(handle.RootElement, "receipt_path", "receipt_sha256", "request_sha256", "run_id", "schema");
            if (handle.RootElement.GetProperty("schema").GetString() != "run-handle-v1") throw new FormatException("wrong handle schema");
            var requestSha = handle.RootElement.GetProperty("request_sha256").GetString()!;
            if (requestSha != expectedRequestSha256) return new(1, "RUN_HANDLE_REQUEST_MISMATCH caller digest differs\n");
            var runId = handle.RootElement.GetProperty("run_id").GetString()!;
            RunRequest.RequireRunId(runId);
            var runRoot = Path.Combine(outputRoot, runId);
            if (!Directory.Exists(runRoot) || Path.GetFullPath(runDirectories[0]) != Path.GetFullPath(runRoot))
                throw new FormatException("handle run_id has no unique final directory");
            var receiptRelative = handle.RootElement.GetProperty("receipt_path").GetString()!;
            if (receiptRelative != "receipt.json") throw new FormatException("receipt_path must be receipt.json");
            var receiptPath = RunPath.ResolveContained(runRoot, receiptRelative, requireExists: true);
            var receiptBytes = File.ReadAllBytes(receiptPath);
            if (RunHandleDigests.Domain("receipt-v1", receiptBytes) != handle.RootElement.GetProperty("receipt_sha256").GetString())
                throw new FormatException("receipt digest mismatch");
            using var receipt = RunHandleJson.ParseCanonical(receiptBytes);
            RunHandleJson.RequireFields(receipt.RootElement, "artifact_set_sha256", "artifacts", "base_tree_sha256", "cross_artifact_sha256", "pass", "producer_build_sha256", "request_sha256", "run_id", "schema", "source_date_epoch", "source_tree_sha256", "verifiers");
            if (receipt.RootElement.GetProperty("schema").GetString() != "receipt-v1"
                || receipt.RootElement.GetProperty("request_sha256").GetString() != expectedRequestSha256
                || receipt.RootElement.GetProperty("run_id").GetString() != runId
                || !receipt.RootElement.GetProperty("pass").GetBoolean()) throw new FormatException("receipt identity mismatch");
            var reconstructedRequest = RunHandleJson.Write(new Dictionary<string, object?>
            {
                ["schema"] = "run-request-v1",
                ["run_id"] = runId,
                ["source_tree_sha256"] = receipt.RootElement.GetProperty("source_tree_sha256").GetString(),
                ["base_tree_sha256"] = receipt.RootElement.GetProperty("base_tree_sha256").GetString(),
                ["producer_build_sha256"] = receipt.RootElement.GetProperty("producer_build_sha256").GetString(),
                ["source_date_epoch"] = receipt.RootElement.GetProperty("source_date_epoch").GetInt64(),
                ["expected_artifact_inventory_sha256"] = RunHandleDigests.Inventory(inventory),
            });
            _ = RunRequest.Parse(reconstructedRequest);
            if (Convert.ToHexStringLower(SHA256.HashData(reconstructedRequest)) != expectedRequestSha256)
                throw new FormatException("recomputed request digest mismatch");
            var expected = RunHandleDigests.Ordered(inventory).ToArray();
            var actual = receipt.RootElement.GetProperty("artifacts").EnumerateArray().ToArray();
            if (actual.Length != expected.Length) throw new FormatException("artifact inventory count mismatch");
            var expectedFiles = expected.Select(static item => item.Path).Append("receipt.json").ToHashSet(StringComparer.Ordinal);
            var actualFiles = Directory.EnumerateFiles(runRoot, "*", SearchOption.AllDirectories)
                .Select(path => Path.GetRelativePath(runRoot, path).Replace(Path.DirectorySeparatorChar, '/'))
                .ToHashSet(StringComparer.Ordinal);
            if (!actualFiles.SetEquals(expectedFiles)) throw new FormatException("run directory file closure mismatch");
            var canonicalArtifacts = new List<Dictionary<string, object?>>();
            for (var index = 0; index < expected.Length; index++)
            {
                RunHandleJson.RequireFields(actual[index], "artifact_id", "mode", "path", "sha256");
                var item = expected[index];
                if (actual[index].GetProperty("artifact_id").GetString() != item.ArtifactId
                    || actual[index].GetProperty("path").GetString() != item.Path
                    || actual[index].GetProperty("mode").GetString() != item.Mode) throw new FormatException("artifact inventory projection mismatch");
                var artifactPath = RunPath.ResolveContained(runRoot, item.Path, requireExists: true);
                if (!OperatingSystem.IsWindows())
                {
                    var actualMode = "100" + Convert.ToString((int)File.GetUnixFileMode(artifactPath) & 0x1ff, 8)!.PadLeft(3, '0');
                    if (actualMode != item.Mode) throw new FormatException("artifact filesystem mode mismatch");
                }
                var digest = Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(artifactPath)));
                if (actual[index].GetProperty("sha256").GetString() != digest) throw new FormatException("artifact bytes mismatch");
                canonicalArtifacts.Add(new Dictionary<string, object?> { ["artifact_id"] = item.ArtifactId, ["path"] = item.Path, ["sha256"] = digest, ["mode"] = item.Mode });
            }
            if (RunHandleDigests.Domain("artifact-set-v1", RunHandleJson.Write(canonicalArtifacts)) != receipt.RootElement.GetProperty("artifact_set_sha256").GetString())
                throw new FormatException("artifact set digest mismatch");
            var artifactSetSha = receipt.RootElement.GetProperty("artifact_set_sha256").GetString()!;
            var verifierBytes = RunHandleJson.Write(new Dictionary<string, object?> { ["artifact_set_sha256"] = artifactSetSha, ["pass"] = true });
            var verifiers = receipt.RootElement.GetProperty("verifiers");
            if (verifiers.GetArrayLength() != 1
                || verifiers[0].GetProperty("id").GetString() != "artifact-byte-verifier-v1"
                || verifiers[0].GetProperty("disposition").GetString() != "pass"
                || verifiers[0].GetProperty("result_sha256").GetString() != RunHandleDigests.Domain("artifact-byte-verifier-v1", verifierBytes))
                throw new FormatException("verifier result mismatch");
            var cross = RunHandleJson.Write(new Dictionary<string, object?>
            {
                ["request_sha256"] = expectedRequestSha256,
                ["source_tree_sha256"] = receipt.RootElement.GetProperty("source_tree_sha256").GetString(),
                ["base_tree_sha256"] = receipt.RootElement.GetProperty("base_tree_sha256").GetString(),
                ["producer_build_sha256"] = receipt.RootElement.GetProperty("producer_build_sha256").GetString(),
                ["artifact_set_sha256"] = artifactSetSha,
                ["verifiers"] = JsonSerializer.Deserialize<object>(verifiers.GetRawText()),
            });
            if (Convert.ToHexStringLower(SHA256.HashData(cross)) != receipt.RootElement.GetProperty("cross_artifact_sha256").GetString())
                throw new FormatException("cross artifact digest mismatch");
            return new(0, "RUN_HANDLE_VERIFIED\n", requestSha);
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException or FormatException or JsonException)
        {
            return new(1, "RUN_HANDLE_INVALID " + exception.Message + "\n");
        }
    }
}

internal sealed record RunRequest(string RunId, string SourceTreeSha256, string BaseTreeSha256, string ProducerBuildSha256, long SourceDateEpoch, string ExpectedInventorySha256, byte[] CanonicalBytes)
{
    internal static RunRequest Parse(ReadOnlySpan<byte> bytes)
    {
        using var document = RunHandleJson.ParseCanonical(bytes.ToArray());
        var root = document.RootElement;
        RunHandleJson.RequireFields(root, "base_tree_sha256", "expected_artifact_inventory_sha256", "producer_build_sha256", "run_id", "schema", "source_date_epoch", "source_tree_sha256");
        if (root.GetProperty("schema").GetString() != "run-request-v1") throw new FormatException("wrong request schema");
        var runId = root.GetProperty("run_id").GetString()!; RequireRunId(runId);
        var source = root.GetProperty("source_tree_sha256").GetString()!; RequireSha(source, "source_tree_sha256");
        var baseline = root.GetProperty("base_tree_sha256").GetString()!; RequireSha(baseline, "base_tree_sha256");
        var build = root.GetProperty("producer_build_sha256").GetString()!; RequireSha(build, "producer_build_sha256");
        var inventory = root.GetProperty("expected_artifact_inventory_sha256").GetString()!; RequireSha(inventory, "expected_artifact_inventory_sha256");
        if (!root.GetProperty("source_date_epoch").TryGetInt64(out var epoch) || epoch < 0) throw new FormatException("source_date_epoch invalid");
        return new(runId, source, baseline, build, epoch, inventory, bytes.ToArray());
    }

    internal static void RequireSha(string value, string name)
    {
        if (value.Length != 64 || value.Any(static item => item is not (>= '0' and <= '9') and not (>= 'a' and <= 'f'))) throw new FormatException(name + " must be lowercase sha256");
    }
    internal static void RequireRunId(string value)
    {
        if (value.Length != 32 || value.Any(static item => item is not (>= '0' and <= '9') and not (>= 'a' and <= 'f'))) throw new FormatException("run_id invalid");
    }
}

internal static class RunHandleJson
{
    internal static byte[] Write(object value)
    {
        var raw = JsonSerializer.SerializeToUtf8Bytes(value);
        using var document = JsonDocument.Parse(raw);
        return StructuredCanonicalWriter.WriteJson(document.RootElement).ToArray();
    }
    internal static JsonDocument ParseCanonical(byte[] bytes)
    {
        var document = JsonDocument.Parse(bytes, new JsonDocumentOptions { AllowTrailingCommas = false, CommentHandling = JsonCommentHandling.Disallow });
        var canonical = StructuredCanonicalWriter.WriteJson(document.RootElement);
        if (!canonical.AsSpan().SequenceEqual(bytes)) { document.Dispose(); throw new FormatException("JSON is not RFC 8785 canonical"); }
        return document;
    }
    internal static void RequireFields(JsonElement value, params string[] expected)
    {
        if (value.ValueKind != JsonValueKind.Object) throw new FormatException("record must be object");
        var actual = value.EnumerateObject().Select(static item => item.Name).Order(StringComparer.Ordinal).ToArray();
        var wanted = expected.Order(StringComparer.Ordinal).ToArray();
        if (!actual.SequenceEqual(wanted, StringComparer.Ordinal)) throw new FormatException("record has unknown or missing fields");
    }
}

internal static class RunPath
{
    internal static void Validate(string relative)
    {
        if (string.IsNullOrEmpty(relative) || Path.IsPathFullyQualified(relative) || relative.Contains('\\')) throw new FormatException("path is not canonical relative slash path");
        var segments = relative.Split('/');
        if (segments.Any(static item => item.Length == 0 || item is "." or "..")) throw new FormatException("path contains empty/dot segment");
        if (!relative.IsNormalized(NormalizationForm.FormC)) throw new FormatException("path is not NFC");
    }
    internal static string ResolveContained(string root, string relative, bool requireExists)
    {
        Validate(relative);
        var rootFull = Path.GetFullPath(root).TrimEnd(Path.DirectorySeparatorChar) + Path.DirectorySeparatorChar;
        var current = root.TrimEnd(Path.DirectorySeparatorChar);
        foreach (var segment in relative.Split('/'))
        {
            current = Path.Combine(current, segment);
            if ((File.Exists(current) || Directory.Exists(current)) && File.GetAttributes(current).HasFlag(FileAttributes.ReparsePoint)) throw new FormatException("symlink in path");
        }
        var full = Path.GetFullPath(current);
        if (!full.StartsWith(rootFull, StringComparison.Ordinal)) throw new FormatException("path escapes root");
        if (requireExists && !File.Exists(full)) throw new FormatException("path does not exist");
        return full;
    }
}

internal static class RunDurability
{
    internal static void SyncDirectoryTree(string root)
    {
        foreach (var directory in Directory.EnumerateDirectories(root, "*", SearchOption.AllDirectories).OrderByDescending(static path => path.Length)) SyncDirectory(directory);
        SyncDirectory(root);
    }
    internal static void SyncDirectory(string path)
    {
        var descriptor = open(path, 0);
        if (descriptor < 0) throw new IOException("open directory for fsync failed");
        try { if (fsync(descriptor) != 0) throw new IOException("directory fsync failed"); }
        finally { _ = close(descriptor); }
    }
    [DllImport("libc", CharSet = CharSet.Ansi, SetLastError = true)] private static extern int open(string path, int flags);
    [DllImport("libc", SetLastError = true)] private static extern int fsync(int descriptor);
    [DllImport("libc", SetLastError = true)] private static extern int close(int descriptor);
}
