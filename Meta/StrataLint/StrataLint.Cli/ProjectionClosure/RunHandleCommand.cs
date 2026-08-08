using System.Collections.Immutable;
using System.Diagnostics;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Scribe;

namespace StrataLint.Cli;

internal static class RunHandleCommand
{
    internal static ExplicitCommandResult CreateRequest(
        string repositoryRoot,
        IReadOnlyList<string> arguments)
    {
        if (arguments.Count != 6)
            return Usage("run-request --manifest SHA256 --run-id HEX32 --out FILE");
        var values = arguments.Chunk(2).ToDictionary(static pair => pair[0], static pair => pair[1], StringComparer.Ordinal);
        if (values.Count != 3
            || !values.TryGetValue("--manifest", out var manifest)
            || !values.TryGetValue("--run-id", out var runId)
            || !values.TryGetValue("--out", out var output))
            return Usage("run-request --manifest SHA256 --run-id HEX32 --out FILE");
        try
        {
            RunRequest.RequireSha(manifest, "MANIFEST");
            RunRequest.RequireRunId(runId);
            var bytes = Request(
                manifest,
                runId,
                RunHandleDigests.Inventory(Inventory(repositoryRoot)),
                0);
            File.WriteAllBytes(output, bytes);
            return new(0, "RUN_REQUEST_WRITTEN\n", string.Empty);
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException
            or FormatException or ArgumentException)
        {
            return new(1, string.Empty, "RUN_REQUEST_INVALID " + exception.Message + "\n");
        }
    }

    internal static ExplicitCommandResult CanaryScope(IReadOnlyList<string> arguments)
    {
        if (arguments.Count != 2 || arguments[0] != "--out" || string.IsNullOrWhiteSpace(arguments[1]))
            return Usage("refactor-pr-a-canary-scope --out FILE");
        var tuples = PrAMetamorphicVerifier.CanaryScope()
            .Select(PrAMetamorphicVerifier.DescribeEnvironment)
            .ToArray();
        var bytes = RunHandleJson.Write(new Dictionary<string, object?>
        {
            ["schema"] = "refactor-pr-a-canary-scope-v1",
            ["lane"] = "canary",
            ["real_rebuilds_run"] = 0,
            ["canary_deferred_count"] = tuples.Length,
            ["deferred_env_tuples"] = tuples,
            ["execution"] = "scope-only",
        });
        Directory.CreateDirectory(Path.GetDirectoryName(Path.GetFullPath(arguments[1]))!);
        File.WriteAllBytes(arguments[1], bytes);
        return new(0, $"PR_A_CANARY_SCOPE tuples={tuples.Length} execution=scope-only\n", string.Empty);
    }

    internal static ExplicitCommandResult CanaryVerify(string repositoryRoot, IReadOnlyList<string> arguments)
    {
        if (!TryPair(arguments, "--manifest", "--out", out var manifest, out var output))
            return Usage("refactor-pr-a-canary-verify --manifest SHA256 --out FILE");
        try
        {
            RunRequest.RequireSha(manifest, "MANIFEST");
            var tuples = PrAMetamorphicVerifier.CanaryScope()
                .Select(PrAMetamorphicVerifier.DescribeEnvironment).ToArray();
            WriteCanary(output, manifest, 0, tuples.Length, tuples, "running", false, []);
            var inventory = Inventory(repositoryRoot);
            using var rebuilds = new PrARealRebuildRunner(repositoryRoot, inventory, cacheByEnvironment: true);
            var result = PrAMetamorphicVerifier.VerifyCanary(testCase => rebuilds.Rebuild(
                testCase, manifest, manifest[..32], RunHandleDigests.Inventory(inventory), BuildSha()));
            WriteCanary(output, manifest, result.RealRebuildsRun, 0, [], "complete", result.Pass, result.Diagnostics);
            return new(result.ExitCode, result.Pass ? "PR_A_CANARY_OK\n" : string.Empty,
                result.Pass ? string.Empty : string.Join("\n", result.Diagnostics) + "\n");
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException or FormatException
            or JsonException or InvalidOperationException or TimeoutException)
        {
            return new(2, string.Empty, "PR_A_CANARY_INVALID " + exception.Message + "\n");
        }
    }

    private static void WriteCanary(string output, string manifest, int rebuilds, int deferredCount,
        string[] deferred, string execution, bool pass, IEnumerable<string> diagnostics)
    {
        var bytes = RunHandleJson.Write(new Dictionary<string, object?>
        {
            ["schema"] = "refactor-pr-a-verification-v1", ["manifest_sha256"] = manifest,
            ["lane"] = "canary", ["real_rebuilds_run"] = rebuilds,
            ["canary_deferred_count"] = deferredCount, ["deferred_env_tuples"] = deferred,
            ["execution"] = execution, ["diagnostics"] = diagnostics.ToArray(), ["pass"] = pass,
        });
        Directory.CreateDirectory(Path.GetDirectoryName(Path.GetFullPath(output))!);
        File.WriteAllBytes(output, bytes);
    }

    internal static ExplicitCommandResult Produce(string repositoryRoot, IReadOnlyList<string> arguments)
    {
        if (!TryPair(arguments, "--request", "--output-root", out var request, out var outputRoot)) return Usage("run-produce --request FILE --output-root DIR");
        var result = RunHandleProducer.Produce(repositoryRoot, outputRoot, File.ReadAllBytes(request), Inventory(repositoryRoot));
        return new(result.ExitCode, result.ExitCode == 0 ? result.Diagnostic : string.Empty, result.ExitCode == 0 ? string.Empty : result.Diagnostic);
    }

    internal static ExplicitCommandResult Consume(string repositoryRoot, IReadOnlyList<string> arguments)
    {
        if (!TryPair(arguments, "--output-root", "--expected-request-sha256", out var outputRoot, out var expected)) return Usage("run-consume --output-root DIR --expected-request-sha256 SHA256");
        var result = RunHandleConsumer.Consume(outputRoot, expected, Inventory(repositoryRoot));
        return new(result.ExitCode, result.ExitCode == 0 ? result.Diagnostic : string.Empty, result.ExitCode == 0 ? string.Empty : result.Diagnostic);
    }

    internal static ExplicitCommandResult Verify(string repositoryRoot, IReadOnlyList<string> arguments)
    {
        if (!TryPair(arguments, "--manifest", "--out", out var manifest, out var output)) return Usage("refactor-pr-a-verify --manifest SHA256 --out FILE");
        try
        {
            RunRequest.RequireSha(manifest, "MANIFEST");
            if (string.IsNullOrWhiteSpace(output)) throw new FormatException("OUT must be non-empty");
            var inventory = Inventory(repositoryRoot);
            var inventorySha = RunHandleDigests.Inventory(inventory);
            var runId = manifest[..32];
            var producerBuildSha = BuildSha();
            var stopwatch = Stopwatch.StartNew();
            using var rebuilds = new PrARealRebuildRunner(repositoryRoot, inventory);
            var verificationStopwatch = Stopwatch.StartNew();
            rebuilds.PrepareRequiredRebuilds(manifest, runId, inventorySha, producerBuildSha);
            var result = PrAMetamorphicVerifier.VerifyRequired(testCase =>
                rebuilds.Rebuild(testCase, manifest, runId, inventorySha, producerBuildSha));
            verificationStopwatch.Stop();
            stopwatch.Stop();
            var diagnostics = result.Diagnostics;
            var pass = result.Pass;
            var resultBytes = RunHandleJson.Write(new Dictionary<string, object?>
            {
                ["schema"] = "refactor-pr-a-verification-v1",
                ["manifest_sha256"] = manifest,
                ["pinned_commit"] = rebuilds.PinnedCommit,
                ["cases_run"] = result.CasesRun,
                ["lane"] = result.Lane,
                ["real_rebuilds_run"] = result.RealRebuildsRun,
                ["canary_deferred_count"] = result.CanaryDeferredCount,
                ["deferred_env_tuples"] = result.DeferredEnvTuples.ToArray(),
                ["elapsed_milliseconds"] = stopwatch.ElapsedMilliseconds,
                ["phase_elapsed_milliseconds"] = rebuilds.PhaseElapsedMilliseconds
                    .Append(new KeyValuePair<string, long>("verification", verificationStopwatch.ElapsedMilliseconds))
                    .OrderBy(static item => item.Key, StringComparer.Ordinal)
                    .ToDictionary(static item => item.Key, static item => item.Value, StringComparer.Ordinal),
                ["diagnostics"] = diagnostics.ToArray(),
                ["spec_deviations"] = Array.Empty<string>(),
                ["pass"] = pass,
            });
            Directory.CreateDirectory(Path.GetDirectoryName(Path.GetFullPath(output))!);
            File.WriteAllBytes(output, resultBytes);
            return new(result.ExitCode, pass ? "PR_A_VERIFY_OK\n" : string.Empty, pass ? string.Empty : string.Join("\n", diagnostics) + "\n");
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException or FormatException or JsonException or InvalidOperationException or TimeoutException)
        {
            return new(2, string.Empty, "PR_A_VERIFY_INVALID " + exception.Message + "\n");
        }
    }

    internal static ImmutableArray<RunArtifactInventoryItem> Inventory(string repositoryRoot) =>
        FileMapLoader.LoadRepository(repositoryRoot).Entries
            .Where(static entry => entry.Kind is FileMapKind.Generated && entry.ArtifactId != "none")
            .Select(static entry => new RunArtifactInventoryItem(entry.ArtifactId, entry.Pattern, entry.Mode!))
            .OrderBy(static entry => entry.Path, StringComparer.Ordinal)
            .ThenBy(static entry => entry.ArtifactId, StringComparer.Ordinal)
            .ToImmutableArray();

    internal static byte[] Request(
        string manifest,
        string runId,
        string inventorySha,
        long epoch,
        string? producerBuildSha = null) => RunHandleJson.Write(new Dictionary<string, object?>
    {
        ["schema"] = "run-request-v1", ["run_id"] = runId,
        ["source_tree_sha256"] = manifest, ["base_tree_sha256"] = manifest,
        ["producer_build_sha256"] = producerBuildSha ?? BuildSha(), ["source_date_epoch"] = epoch,
        ["expected_artifact_inventory_sha256"] = inventorySha,
    });

    private static string BuildSha()
    {
        var path = typeof(RunHandleCommand).Assembly.Location;
        return Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(path)));
    }

    internal static PrARunSnapshot Snapshot(string outputRoot, string runId)
    {
        var runRoot = Path.Combine(outputRoot, runId);
        var receiptBytes = File.ReadAllBytes(Path.Combine(runRoot, "receipt.json"));
        var handleBytes = File.ReadAllBytes(Path.Combine(outputRoot, "handle.json"));
        using var receipt = JsonDocument.Parse(receiptBytes);
        var artifacts = receipt.RootElement.GetProperty("artifacts").EnumerateArray().Select(item =>
        {
            var path = item.GetProperty("path").GetString()!;
            return new PrAArtifact(item.GetProperty("artifact_id").GetString()!, path, item.GetProperty("mode").GetString()!, item.GetProperty("sha256").GetString()!, File.ReadAllBytes(Path.Combine(runRoot, path)).ToImmutableArray());
        }).ToImmutableArray();
        var verifiers = receipt.RootElement.GetProperty("verifiers").EnumerateArray().ToImmutableDictionary(
            static item => item.GetProperty("id").GetString()!,
            static item => Encoding.UTF8.GetBytes(item.GetProperty("result_sha256").GetString()!).ToImmutableArray(),
            StringComparer.Ordinal);
        return new(artifacts, Encoding.UTF8.GetString(receiptBytes), Encoding.UTF8.GetString(handleBytes), verifiers);
    }

    private static bool TryPair(IReadOnlyList<string> args, string firstName, string secondName, out string first, out string second)
    {
        first = second = string.Empty;
        if (args.Count != 4) return false;
        for (var index = 0; index < args.Count; index += 2)
        {
            if (args[index] == firstName && first.Length == 0) first = args[index + 1];
            else if (args[index] == secondName && second.Length == 0) second = args[index + 1];
            else return false;
        }
        return first.Length != 0 && second.Length != 0;
    }

    private static ExplicitCommandResult Usage(string usage) => new(2, string.Empty, "USAGE: StrataLint " + usage + "\n");
}
