using System.Reflection;
using Xunit.Abstractions;
using Xunit.Sdk;

[assembly: TestFramework("StrataLint.Tests.TestScratchFramework", "StrataLint.Tests")]

namespace StrataLint.Tests;

internal static class TestDirectoryCleanup
{
    internal const int MaximumAttempts = 40;
    private static readonly TimeSpan RetryDelay = TimeSpan.FromMilliseconds(25);

    internal static void DeleteRecursively(string path) =>
        DeleteRecursively(path, Directory.Delete, Thread.Sleep);

    internal static void DeleteRecursively(
        string path,
        Action<string, bool> deleteDirectory,
        Action<TimeSpan> delay)
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
                delay(RetryDelay);
            }
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
    private bool disposed;

    static TestScratchRoot() =>
        AppDomain.CurrentDomain.ProcessExit += static (_, _) => DisposeCurrentAtExit();

    internal TestScratchRoot() =>
        Path = Directory.CreateTempSubdirectory("stratalint-tests-").FullName;

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
            TestDirectoryCleanup.DeleteRecursively(Path);
        }
    }

    private static void DisposeCurrentAtExit()
    {
        try
        {
            TestScratchRoot? root;
            lock (CurrentGate)
            {
                root = current;
                current = null;
            }

            root?.Dispose();
        }
        catch (IOException)
        {
        }
        catch (UnauthorizedAccessException)
        {
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
