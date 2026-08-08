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

    internal PrARealRebuildRunner(
        string repositoryRoot,
        ImmutableArray<RunArtifactInventoryItem> inventory)
    {
        this.repositoryRoot = Path.GetFullPath(repositoryRoot);
        this.inventory = inventory;
        scratchRoot = Path.Combine(Path.GetTempPath(), "stratalint-pr-a-rebuild-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(scratchRoot);
        pinnedCommit = Git(this.repositoryRoot, ["rev-parse", "--verify", "HEAD^{commit}"]).Trim();
        leanReport = PrepareLeanReport();
        PrepareCheckout("checkout-a");
        PrepareCheckout("checkout-b");
    }

    internal string PinnedCommit => pinnedCommit;

    internal PrARealRebuildOutcome Rebuild(
        PrAMatrixCase testCase,
        string manifest,
        string runId,
        string inventorySha,
        string producerBuildSha)
    {
        if (!checkouts.TryGetValue(testCase.Checkout, out var checkout))
            throw new InvalidOperationException($"unknown checkout {testCase.Checkout}");

        var key = EnvironmentKey(testCase);
        var generatorRan = !generated.TryGetValue(key, out var artifacts);
        var sourceRoot = checkout;
        if (generatorRan)
        {
            RestoreCleanCheckout(checkout);
            var echo = RunEnvironment(
                checkout,
                testCase,
                ["make", "--no-print-directory", "echo-residual-summary", $"BASE={pinnedCommit}^"]);
            File.WriteAllBytes(Path.Combine(checkout, "Generated", "echo-residual-summary.md"), echo.StandardOutput);
            _ = RunEnvironment(checkout, testCase, ["make", "--no-print-directory", "emit"]);
            artifacts = ReadArtifacts(checkout);
            generated.Add(key, artifacts);
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
        File.Copy(leanReport, report, overwrite: true);
        Run("make", ["--no-print-directory", "dotnet"], checkout, TimeSpan.FromMinutes(20));
        RequireCleanTrackedTree(checkout);
    }

    private void RestoreCleanCheckout(string checkout)
    {
        var arguments = new List<string> { "restore", "--source=HEAD", "--" };
        arguments.AddRange(inventory.Select(static item => item.Path));
        Run("git", arguments, checkout, TimeSpan.FromMinutes(2));
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
        IReadOnlyList<string> command)
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
        arguments.AddRange(command);
        return Run("/usr/bin/env", arguments, checkout, CommandTimeout);
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
