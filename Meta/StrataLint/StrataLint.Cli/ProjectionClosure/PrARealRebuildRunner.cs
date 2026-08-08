using System.Collections.Immutable;
using System.Diagnostics;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed class PrARealRebuildRunner : IDisposable
{
    private static readonly TimeSpan CommandTimeout = TimeSpan.FromMinutes(20);
    private readonly string repositoryRoot;
    private readonly ImmutableArray<RunArtifactInventoryItem> inventory;
    private readonly string scratchRoot;
    private readonly string pinnedCommit;
    private readonly string leanReport;
    private readonly Dictionary<string, string> checkouts = new(StringComparer.Ordinal);
    private readonly Dictionary<string, ImmutableArray<PrAArtifact>> generated = new(StringComparer.Ordinal);
    private readonly Action<string, string>? checkoutMutation;
    private readonly bool validateAfterMutation;
    private readonly bool cacheByEnvironment;

    internal PrARealRebuildRunner(
        string repositoryRoot,
        ImmutableArray<RunArtifactInventoryItem> inventory,
        Action<string, string>? checkoutMutation = null,
        bool validateAfterMutation = false,
        bool cacheByEnvironment = false)
    {
        this.repositoryRoot = Path.GetFullPath(repositoryRoot);
        this.inventory = inventory;
        this.checkoutMutation = checkoutMutation;
        this.validateAfterMutation = validateAfterMutation;
        this.cacheByEnvironment = cacheByEnvironment;
        scratchRoot = Path.Combine(Path.GetTempPath(), "stratalint-pr-a-rebuild-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(scratchRoot);
        pinnedCommit = Git(this.repositoryRoot, ["rev-parse", "--verify", "HEAD^{commit}"]).Trim();
        leanReport = PrepareLeanReport();
        PrepareCheckout("checkout-a");
        PrepareCheckout("checkout-b");
    }

    internal string PinnedCommit => pinnedCommit;

    internal static T InPinnedCheckout<T>(string repositoryRoot, string commit, Func<string, T> action)
    {
        var scratch = Path.Combine(Path.GetTempPath(), "stratalint-quotient-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(scratch);
        var checkout = Path.Combine(scratch, "checkout");
        try
        {
            Run("git", ["worktree", "add", "--detach", checkout, commit], repositoryRoot, TimeSpan.FromMinutes(2));
            Run("make", ["--no-print-directory", "dotnet"], checkout, TimeSpan.FromMinutes(20));
            return action(checkout);
        }
        finally
        {
            _ = BoundedProcessRunner.Run("git", ["worktree", "remove", "--force", checkout],
                repositoryRoot, TimeSpan.FromMinutes(2), 1024 * 1024);
            if (Directory.Exists(scratch)) Directory.Delete(scratch, recursive: true);
        }
    }

    internal PrARealRebuildOutcome Rebuild(
        PrAMatrixCase testCase,
        string manifest,
        string runId,
        string inventorySha,
        string producerBuildSha)
    {
        if (!checkouts.TryGetValue(testCase.Checkout, out var checkout))
            throw new InvalidOperationException($"unknown checkout {testCase.Checkout}");

        var key = cacheByEnvironment ? EnvironmentKey(testCase) : testCase.Checkout;
        var generatorRan = !generated.TryGetValue(key, out var artifacts);
        var sourceRoot = checkout;
        if (generatorRan)
        {
            RestoreCleanCheckout(checkout);
            checkoutMutation?.Invoke(testCase.Checkout, checkout);
            if (validateAfterMutation) RequireCleanTrackedTree(checkout);
            _ = RunEnvironment(checkout, testCase,
                ["/bin/bash", "Meta/StrataLint/scripts/scribe.sh", "bootstrap"]);
            var bootstrapRoot = CreateBootstrapReceipt(
                checkout, manifest, runId, inventorySha, producerBuildSha);
            var echo = RunEnvironment(
                checkout,
                testCase,
                ["make", "--no-print-directory", "echo-residual-summary", $"BASE={pinnedCommit}^"],
                bootstrapRoot);
            var echoPath = Path.Combine(checkout, "Generated", "echo-residual-summary.md");
            Directory.CreateDirectory(Path.GetDirectoryName(echoPath)!);
            File.WriteAllBytes(echoPath, echo.StandardOutput);
            _ = RunEnvironment(checkout, testCase, ["make", "--no-print-directory", "emit"], bootstrapRoot);
            artifacts = ReadArtifacts(checkout);
            generated.Add(key, artifacts);
            Directory.Delete(bootstrapRoot, recursive: true);
        }
        else
        {
            sourceRoot = Path.Combine(scratchRoot, "cached-source-" + Guid.NewGuid().ToString("N"));
            Directory.CreateDirectory(sourceRoot);
            foreach (var artifact in artifacts)
            {
                var path = Path.Combine(sourceRoot, artifact.Path);
                Directory.CreateDirectory(Path.GetDirectoryName(path)!);
                File.WriteAllBytes(path, artifact.Bytes.AsSpan());
            }
        }

        var outputRoot = Path.Combine(scratchRoot, testCase.OutputRoot + "-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(outputRoot);
        try
        {
            var request = RunHandleCommand.Request(
                manifest,
                runId,
                inventorySha,
                testCase.SourceDateEpoch,
                producerBuildSha);
            var produced = RunHandleProducer.Produce(sourceRoot, outputRoot, request, inventory);
            if (produced.ExitCode != 0) throw new InvalidOperationException(produced.Diagnostic.Trim());
            var consumed = RunHandleConsumer.Consume(outputRoot, produced.RequestSha256, inventory);
            if (consumed.ExitCode != 0) throw new InvalidOperationException(consumed.Diagnostic.Trim());
            return new PrARealRebuildOutcome(RunHandleCommand.Snapshot(outputRoot, runId), generatorRan);
        }
        finally
        {
            if (Directory.Exists(outputRoot)) Directory.Delete(outputRoot, recursive: true);
            if (sourceRoot != checkout && Directory.Exists(sourceRoot)) Directory.Delete(sourceRoot, recursive: true);
        }
    }

    public void Dispose()
    {
        foreach (var checkout in checkouts.Values)
        {
            _ = BoundedProcessRunner.Run(
                "git",
                ["worktree", "remove", "--force", checkout],
                repositoryRoot,
                TimeSpan.FromMinutes(2),
                1024 * 1024);
        }
        if (Directory.Exists(scratchRoot)) Directory.Delete(scratchRoot, recursive: true);
    }

    private string PrepareLeanReport()
    {
        Run("make", ["--no-print-directory", "lean-report"], repositoryRoot, TimeSpan.FromHours(3));
        var path = Path.Combine(repositoryRoot, ".lake", "build", "stratalint", "raw-lean-report.json");
        if (!File.Exists(path)) throw new InvalidOperationException("canonical raw Lean report is absent");
        return path;
    }

    private void PrepareCheckout(string name)
    {
        var checkout = Path.Combine(scratchRoot, name);
        Run("git", ["worktree", "add", "--detach", checkout, pinnedCommit], repositoryRoot, TimeSpan.FromMinutes(2));
        checkouts.Add(name, checkout);
        var report = Path.Combine(checkout, ".lake", "build", "stratalint", "raw-lean-report.json");
        Directory.CreateDirectory(Path.GetDirectoryName(report)!);
        foreach (var suffix in new[] { string.Empty, ".sha256", ".input.attestation", ".provenance.json" })
            File.Copy(leanReport + suffix, report + suffix, overwrite: true);
        Run("make", ["--no-print-directory", "dotnet"], checkout, TimeSpan.FromMinutes(20));
        RequireCleanTrackedTree(checkout);
    }

    private void RestoreCleanCheckout(string checkout)
    {
        Run("git", ["restore", "--source=HEAD", "--", "."], checkout, TimeSpan.FromMinutes(2));
        var tracked = Git(checkout, ["ls-files", "-z"])
            .Split('\0', StringSplitOptions.RemoveEmptyEntries)
            .ToHashSet(StringComparer.Ordinal);
        foreach (var item in inventory.Where(item => !tracked.Contains(item.Path)))
        {
            var path = Path.Combine(checkout, item.Path);
            if (File.Exists(path)) File.Delete(path);
        }
        RequireCleanTrackedTree(checkout);
    }

    private ImmutableArray<PrAArtifact> ReadArtifacts(string checkout) => inventory.Select(item =>
    {
        var bytes = File.ReadAllBytes(Path.Combine(checkout, item.Path));
        return new PrAArtifact(
            item.ArtifactId,
            item.Path,
            item.Mode,
            Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(bytes)),
            bytes.ToImmutableArray());
    }).ToImmutableArray();

    private static string EnvironmentKey(PrAMatrixCase item) =>
        $"{item.Checkout}\0{item.Locale}\0{item.Timezone}\0{item.Order}\0{item.Parallelism}\0{item.SourceDateEpoch}";

    private ProcessOutput RunEnvironment(
        string checkout,
        PrAMatrixCase testCase,
        IReadOnlyList<string> command,
        string? receiptRoot = null)
    {
        var arguments = new List<string>
        {
            $"LC_ALL={testCase.Locale}",
            $"LANG={testCase.Locale}",
            $"TZ={testCase.Timezone}",
            $"SOURCE_DATE_EPOCH={testCase.SourceDateEpoch}",
            $"STRATALINT_PR_A_ORDER={testCase.Order}",
            $"STRATALINT_PR_A_PARALLELISM={testCase.Parallelism}",
            "STRATALINT_PR_A_NO_BUILD=1",
        };
        if (receiptRoot is not null) arguments.Add($"STRATALINT_RUN_RECEIPT_ROOT={receiptRoot}");
        arguments.AddRange(command);
        return Run("/usr/bin/env", arguments, checkout, CommandTimeout);
    }

    private string CreateBootstrapReceipt(
        string checkout,
        string manifest,
        string runId,
        string inventorySha,
        string producerBuildSha)
    {
        foreach (var item in inventory)
        {
            var path = Path.Combine(checkout, item.Path);
            if (File.Exists(path)) continue;
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllBytes(path, []);
        }
        var outputRoot = Path.Combine(scratchRoot, "bootstrap-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(outputRoot);
        var request = RunHandleCommand.Request(manifest, runId, inventorySha, 0, producerBuildSha);
        var produced = RunHandleProducer.Produce(checkout, outputRoot, request, inventory);
        if (produced.ExitCode != 0) throw new InvalidOperationException(produced.Diagnostic.Trim());
        var consumed = RunHandleConsumer.Consume(outputRoot, produced.RequestSha256, inventory);
        if (consumed.ExitCode != 0) throw new InvalidOperationException(consumed.Diagnostic.Trim());
        return outputRoot;
    }

    private static void RequireCleanTrackedTree(string root)
    {
        var status = Git(root, ["status", "--porcelain", "--untracked-files=no"]);
        if (status.Length != 0) throw new InvalidOperationException("PR_A_CHECKOUT_NOT_CLEAN " + status.Trim());
    }

    private static string Git(string root, IReadOnlyList<string> arguments) =>
        Encoding.UTF8.GetString(Run("git", arguments, root, TimeSpan.FromMinutes(2)).StandardOutput);

    private static ProcessOutput Run(
        string fileName,
        IEnumerable<string> arguments,
        string workingDirectory,
        TimeSpan timeout)
    {
        var stopwatch = Stopwatch.StartNew();
        var result = BoundedProcessRunner.Run(
            fileName,
            arguments,
            workingDirectory,
            timeout,
            16 * 1024 * 1024);
        if (result.ExitCode == 0) return result;
        var error = Encoding.UTF8.GetString(result.StandardError).Trim();
        var output = Encoding.UTF8.GetString(result.StandardOutput).Trim();
        throw new InvalidOperationException(
            $"PR_A_GENERATOR_FAILED command={fileName} exit={result.ExitCode} elapsed_ms={stopwatch.ElapsedMilliseconds} "
            + (error.Length != 0 ? error : output));
    }
}
