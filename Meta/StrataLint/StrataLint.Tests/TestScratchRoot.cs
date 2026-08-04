using System.Reflection;
using Xunit.Abstractions;
using Xunit.Sdk;

[assembly: TestFramework("StrataLint.Tests.TestScratchFramework", "StrataLint.Tests")]

namespace StrataLint.Tests;

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
            Directory.Delete(Path, recursive: true);
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

    internal TemporaryDirectory() => Path = TestScratchRoot.Current.CreateDirectory();

    internal string Path { get; }

    public void Dispose()
    {
        if (Interlocked.Exchange(ref disposed, 1) != 0)
        {
            return;
        }

        try
        {
            Directory.Delete(Path, recursive: true);
        }
        catch (DirectoryNotFoundException)
        {
        }
    }
}
