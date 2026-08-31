using System.Reflection;
using System.Text.Json;
using Xunit.Abstractions;
using Xunit.Sdk;

[assembly: TestFramework("StrataLint.Tests.TestScratchFramework", "StrataLint.Tests")]

namespace StrataLint.Tests;

internal static class TestEnvironmentBridge
{
    internal static DateTime UtcNow() => TimeProvider.System.GetUtcNow().UtcDateTime;

    internal static void PauseBeforeCleanupRetry()
    {
        using var retryPause = new ManualResetEventSlim(false);
        retryPause.Wait(25);
    }
}

internal static class TestDirectoryCleanup
{
    internal const int MaximumAttempts = 40;

    internal static void DeleteRecursively(string path) =>
        DeleteRecursively(path, Directory.Delete, TestEnvironmentBridge.PauseBeforeCleanupRetry);

    internal static void DeleteRecursively(
        string path,
        Action<string, bool> deleteDirectory,
        Action pauseBeforeRetry)
    {
        for (var attempt = 1; ; attempt++)
        {
            try
            {
                deleteDirectory(path, true);
                return;
            }
            catch (DirectoryNotFoundException)
            {
                return;
            }
            catch (IOException) when (attempt < MaximumAttempts)
            {
                // Git maintenance may detach after commit and briefly repopulate .git/objects.
                pauseBeforeRetry();
            }
        }
    }
}

internal static class TestScratchRootSweeper
{
    internal const string DirectoryPrefix = "stratalint-tests-";
    internal const string LeaseFileName = ".owner.lock";
    private const string RecordPrefix = "TEST_SCRATCH_SWEEP ";

    internal static FileStream CreateOwnerLease(string rootPath) =>
        OpenLease(Path.Combine(rootPath, LeaseFileName), FileMode.CreateNew);

    internal static void SweepAtStartup() =>
        Sweep(Path.GetTempPath(), TestEnvironmentBridge.UtcNow(), Console.Error);

    internal static void Sweep(
        string temporaryPath,
        DateTime utcNow,
        TextWriter diagnostics,
        Action<string>? deleteRecursively = null)
    {
        deleteRecursively ??= TestDirectoryCleanup.DeleteRecursively;

        string[] candidates;
        try
        {
            candidates = Directory.GetDirectories(
                temporaryPath,
                DirectoryPrefix + "*",
                SearchOption.TopDirectoryOnly);
        }
        catch (Exception exception)
        {
            Record(diagnostics, "enumerate", "failed", temporaryPath, exception);
            return;
        }

        foreach (var candidate in candidates)
        {
            if (!Path.GetFileName(candidate).StartsWith(DirectoryPrefix, StringComparison.Ordinal))
            {
                continue;
            }

            SweepCandidate(candidate, utcNow, diagnostics, deleteRecursively);
        }
    }

    private static void SweepCandidate(
        string candidate,
        DateTime utcNow,
        TextWriter diagnostics,
        Action<string> deleteRecursively)
    {
        DateTime lastWriteTimeUtc;
        try
        {
            lastWriteTimeUtc = Directory.GetLastWriteTimeUtc(candidate);
        }
        catch (Exception exception)
        {
            Record(diagnostics, "inspect-age", "failed", candidate, exception);
            return;
        }

        if (lastWriteTimeUtc > utcNow.AddDays(-1))
        {
            return;
        }

        FileStream lease;
        try
        {
            lease = AcquireSweepLease(candidate);
        }
        catch (Exception exception)
        {
            Record(diagnostics, "acquire-lease", "skipped", candidate, exception);
            return;
        }

        try
        {
            lease.Dispose();
        }
        catch (Exception exception)
        {
            Record(diagnostics, "release-lease", "failed", candidate, exception);
            return;
        }

        try
        {
            deleteRecursively(candidate);
        }
        catch (Exception exception)
        {
            Record(diagnostics, "delete", "failed", candidate, exception);
        }
    }

    private static FileStream AcquireSweepLease(string rootPath)
    {
        var leasePath = Path.Combine(rootPath, LeaseFileName);
        try
        {
            return OpenLease(leasePath, FileMode.Open);
        }
        catch (FileNotFoundException)
        {
            return OpenLease(leasePath, FileMode.CreateNew);
        }
    }

    private static FileStream OpenLease(string path, FileMode mode) =>
        new(path, mode, FileAccess.ReadWrite, FileShare.None);

    private static void Record(
        TextWriter diagnostics,
        string operation,
        string status,
        string path,
        Exception exception)
    {
        try
        {
            diagnostics.WriteLine(
                RecordPrefix
                + JsonSerializer.Serialize(new
                {
                    schema = "test-scratch-sweep-v1",
                    operation,
                    status,
                    path,
                    exception_type = exception.GetType().FullName,
                    message = exception.Message,
                }));
        }
        catch (Exception)
        {
            // Startup cleanup must never prevent the test process from running.
        }
    }
}

public sealed class TestScratchFramework : XunitTestFramework
{
    public TestScratchFramework(IMessageSink messageSink)
        : base(messageSink)
    {
    }

    protected override ITestFrameworkExecutor CreateExecutor(AssemblyName assemblyName) =>
        new TestScratchFrameworkExecutor(
            assemblyName,
            SourceInformationProvider,
            DiagnosticMessageSink);
}

internal sealed class TestScratchFrameworkExecutor(
    AssemblyName assemblyName,
    ISourceInformationProvider sourceInformationProvider,
    IMessageSink diagnosticMessageSink)
    : XunitTestFrameworkExecutor(
        assemblyName,
        sourceInformationProvider,
        diagnosticMessageSink)
{
    protected override async void RunTestCases(
        IEnumerable<IXunitTestCase> testCases,
        IMessageSink executionMessageSink,
        ITestFrameworkExecutionOptions executionOptions)
    {
        // Framework disposal can precede execution; the awaited assembly runner is the root owner.
        using var root = TestScratchRoot.Current;
        using var assemblyRunner = new XunitTestAssemblyRunner(
            TestAssembly,
            testCases,
            DiagnosticMessageSink,
            executionMessageSink,
            executionOptions);
        await assemblyRunner.RunAsync();
    }
}

internal sealed class TestScratchRoot : IDisposable
{
    private static readonly object CurrentGate = new();
    private static TestScratchRoot? current;
    private readonly object gate = new();
    private readonly FileStream lease;
    private bool disposed;

    static TestScratchRoot() =>
        TestScratchRootSweeper.SweepAtStartup();

    internal TestScratchRoot()
    {
        Path = Directory.CreateTempSubdirectory("stratalint-tests-").FullName;
        lease = TestScratchRootSweeper.CreateOwnerLease(Path);
    }

    internal static TestScratchRoot Current
    {
        get
        {
            lock (CurrentGate)
            {
                if (current is null || current.disposed)
                {
                    current = new TestScratchRoot();
                }

                return current;
            }
        }
    }

    internal string Path { get; }

    internal string CreateDirectory()
    {
        lock (gate)
        {
            ObjectDisposedException.ThrowIf(disposed, this);
            var path = System.IO.Path.Combine(
                Path,
                "directory-" + Guid.NewGuid().ToString("N"));
            Directory.CreateDirectory(path);
            return path;
        }
    }

    public void Dispose()
    {
        lock (gate)
        {
            if (disposed)
            {
                return;
            }

            disposed = true;
            lease.Dispose();
            TestDirectoryCleanup.DeleteRecursively(Path);
        }
    }
}

internal sealed class TemporaryDirectory : IDisposable
{
    private int disposed;

    internal TemporaryDirectory() : this(TestScratchRoot.Current)
    {
    }

    internal TemporaryDirectory(TestScratchRoot root) => Path = root.CreateDirectory();

    internal string Path { get; }

    public void Dispose()
    {
        if (Interlocked.Exchange(ref disposed, 1) != 0)
        {
            return;
        }

        TestDirectoryCleanup.DeleteRecursively(Path);
    }
}

/// <summary>
/// Script tests build fake executable environments under the test scratch root.
/// Keep their filesystem operations behind the exempt harness assembly boundary.
/// </summary>
internal static class ScriptHarnessScratch
{
    internal static void EnsureDirectory(string path) => Directory.CreateDirectory(path);

    internal static void CopyScriptInto(string sourcePath, string targetPath)
    {
        Directory.CreateDirectory(Path.GetDirectoryName(targetPath)!);
        File.Copy(sourcePath, targetPath);
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    internal static void WriteExecutableStub(string path, string body)
    {
        File.WriteAllText(
            path,
            "#!/usr/bin/env bash\nset -euo pipefail\n" + body + "\n",
            System.Text.Encoding.UTF8);
        File.SetUnixFileMode(
            path,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
    }

    internal static string[] ReadRecordedCalls(string path) =>
        File.Exists(path) ? File.ReadAllLines(path) : [];

    internal static string[] ReadScratchLines(string path) => File.ReadAllLines(path);

    internal static string ReadScratchText(string path) => File.ReadAllText(path);
}
