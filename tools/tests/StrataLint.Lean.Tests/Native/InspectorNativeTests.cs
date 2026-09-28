using System.IO.Compression;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.TestSupport;

namespace StrataLint.Lean.Tests;

public sealed class InspectorNativeTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    // Publication, coordinates and verification use this class's private compiler stage.
    [Theory]
    [InlineData("test_streaming")]
    [InlineData("test_reuse")]
    [InlineData("test_native_records.AxiomClosureTests")]
    [InlineData("test_native_support.GuardedCommandTests")]
    [InlineData("test_native.NativeTests.test_coordinates_use_private_temporary_memo_and_clean_up_failures")]
    public void InspectorArtifactBehavior(string suite) => InspectorNativeTestRunner.Run(compiler, suite);

    [Fact]
    public void PublicationConsumersStartWithPrivateColdProjects() => InspectorNativeTestRunner.Run(compiler,
        "test_native.NativePublicationTests");

    [Fact]
    public void ReportConsumersStartWithPrivateColdProjects() => InspectorNativeTestRunner.Run(compiler,
        "test_native.NativeReportTests");

    [Theory]
    [InlineData(0)]
    [InlineData(7)]
    [InlineData(-1)]
    public void CommandObservationsSurviveSuccessFailureAndGuard(int exit)
    {
        if (OperatingSystem.IsWindows()) return;
        using var observations = new StringWriter();
        string[] arguments = ["python3", "-c", """
            import sys, time
            print('NATIVE_COMMAND_OBSERVATION stdout', flush=True)
            print('NATIVE_COMMAND_OBSERVATION stderr', file=sys.stderr, flush=True)
            if int(sys.argv[1]) < 0: time.sleep(30)
            sys.exit(int(sys.argv[1]))
            """, exit.ToString(System.Globalization.CultureInfo.InvariantCulture)];
        if (exit < 0)
            Assert.Throws<SkipException>(() => InspectorNativeTestRunner.RunObserved(arguments,
                TestRepositoryLayout.FindRoot(), TimeSpan.FromSeconds(1), observations));
        else
            Assert.Equal(exit, InspectorNativeTestRunner.RunObserved(arguments,
                TestRepositoryLayout.FindRoot(), TestBudgets.ScriptProcessHangGuard, observations).ExitCode);
        Assert.Equal(new[] { "NATIVE_COMMAND_OBSERVATION stdout", "NATIVE_COMMAND_OBSERVATION stderr" },
            observations.ToString().Split(Environment.NewLine, StringSplitOptions.RemoveEmptyEntries));
    }
}

internal static class InspectorNativeTestRunner
{
    internal static void Run(InspectorCompilerFixture compiler, string suite)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var clock = TimeProvider.System;
        Console.WriteLine("NATIVE_CASE " + JsonSerializer.Serialize(new { phase = "start", suite, utc = clock.GetUtcNow() }));
        var prepared = clock.GetTimestamp();
        string[] environment = suite.StartsWith("test_native.", StringComparison.Ordinal)
            ? [$"STRATALINT_NATIVE_COMPILER_SEED={compiler.Path}"] : [];
        Console.WriteLine("NATIVE_CASE " + JsonSerializer.Serialize(new { phase = "compiler-ready", suite,
            utc = clock.GetUtcNow(), elapsed_ms = clock.GetElapsedTime(prepared).TotalMilliseconds }));
        var executed = clock.GetTimestamp();
        var result = RunObserved(
            [.. environment, "STRATALINT_NATIVE_COMMAND_OBSERVATION=1", "python3", "-B", "-m", "unittest", suite, "-v"],
            Path.Combine(root, "tools/lean-inspector/tests"), TestBudgets.ReportSupervisorHangGuard);
        Console.WriteLine("NATIVE_CASE " + JsonSerializer.Serialize(new { phase = "child-exit", suite,
            utc = clock.GetUtcNow(), elapsed_ms = clock.GetElapsedTime(executed).TotalMilliseconds, raw_exit = result.ExitCode,
            stdout_bytes = result.StandardOutput.Length, stderr_bytes = result.StandardError.Length }));
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput)
            + Encoding.UTF8.GetString(result.StandardError));
    }

    internal static ProcessOutput RunObserved(string[] arguments, string directory, TimeSpan guard,
        TextWriter? observations = null)
    {
        using var stdout = new MemoryStream();
        using var stderr = new MemoryStream();
        try
        {
            return TestProcessRunner.Run("env", arguments, directory, guard, 1024 * 1024,
                standardOutput: stdout, standardError: stderr);
        }
        finally
        {
            // The guard throws before returning ProcessOutput. Its bounded
            // stream copies still expose completed inner-command observations.
            WriteCommandObservations(stdout.ToArray(), observations);
            WriteCommandObservations(stderr.ToArray(), observations);
        }
    }

    private static void WriteCommandObservations(byte[] output, TextWriter? observations)
    {
        try
        {
            using var reader = new StringReader(Encoding.UTF8.GetString(output));
            while (reader.ReadLine() is { } line)
                if (line.StartsWith("NATIVE_COMMAND_OBSERVATION ", StringComparison.Ordinal))
                    (observations ?? Console.Out).WriteLine(line);
        }
        catch (Exception error) when (error is IOException or ObjectDisposedException)
        {
            // Optional observation must not replace the original child result.
        }
    }
}

public sealed class InspectorCompilerFixture : IDisposable
{
    private sealed record CompilerMaterial(string Name, byte[] CompressedBytes, UnixFileMode? Mode);
    private static readonly Lazy<CompilerMaterial[]> Materials = new(CreateMaterials);
    private readonly TemporaryDirectory temporary = new();
    private readonly Lazy<string> stage;

    public InspectorCompilerFixture()
    {
        stage = new Lazy<string>(() =>
        {
            // Share immutable compiler material; each class keeps its own stage
            // and every Python case still restores into its private cold fixture.
            foreach (var material in Materials.Value)
            {
                var path = System.IO.Path.Combine(temporary.Path, material.Name);
                using (var bytes = new MemoryStream(material.CompressedBytes, writable: false))
                using (var compressed = new GZipStream(bytes, CompressionMode.Decompress))
                using (var file = File.Create(path)) compressed.CopyTo(file);
                if (!OperatingSystem.IsWindows() && material.Mode is { } mode)
                    File.SetUnixFileMode(path, mode);
            }
            return temporary.Path;
        });
    }

    private static CompilerMaterial[] CreateMaterials()
    {
        using var source = new TemporaryDirectory();
        var root = TestRepositoryLayout.FindRoot();
        var result = InspectorNativeTestRunner.RunObserved(
            ["STRATALINT_NATIVE_COMMAND_OBSERVATION=1", "python3", "-B", "test_native_support.py", source.Path],
            System.IO.Path.Combine(root, "tools/lean-inspector/tests"),
            TestBudgets.ReportSupervisorHangGuard);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput)
            + Encoding.UTF8.GetString(result.StandardError));
        var materials = Directory.GetFileSystemEntries(source.Path).Order(StringComparer.Ordinal).Select(path =>
        {
            var info = new FileInfo(path);
            Assert.True(info.Exists && info.LinkTarget is null
                && (info.Attributes & (FileAttributes.Directory | FileAttributes.ReparsePoint | FileAttributes.Device)) == 0,
                "compiler stage must contain only regular files: " + path);
            using var bytes = new MemoryStream();
            using (var file = File.OpenRead(path))
            using (var compressed = new GZipStream(bytes, CompressionLevel.Fastest, leaveOpen: true))
                file.CopyTo(compressed);
            return new CompilerMaterial(info.Name, bytes.ToArray(),
                OperatingSystem.IsWindows() ? null : File.GetUnixFileMode(path));
        }).ToArray();
        Assert.NotEmpty(materials);
        Console.WriteLine($"NATIVE_COMPILER_STAGE files={materials.Length} compressed_bytes={materials.Sum(material => (long)material.CompressedBytes.Length)}");
        return materials;
    }

    public string Path => stage.Value;

    public void Dispose() => temporary.Dispose();
}
