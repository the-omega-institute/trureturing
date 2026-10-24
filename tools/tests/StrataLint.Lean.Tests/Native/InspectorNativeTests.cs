using System.IO.Compression;
using System.Text;
using System.Text.Json;
using StrataLint.TestSupport;

namespace StrataLint.Lean.Tests;

[Collection("Lean cold production integration")]
public sealed class InspectorNativeTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    // Publication, coordinates and verification use this class's private compiler stage.
    [Theory]
    [InlineData("test_streaming")]
    [InlineData("test_entry_regressions.EntryRegressionTests")]
    [InlineData("test_reuse")]
    [InlineData("test_guarded_command.GuardedCommandTests")]
    [InlineData("test_native.NativeTests.test_coordinates_use_private_temporary_memo_and_clean_up_failures")]
    public void InspectorArtifactBehavior(string suite) => InspectorNativeTestRunner.Run(compiler, suite);

    public static IEnumerable<object[]> LocalEntryCases() => InspectorNativeTestRunner.Cases("test_local_entry");

    [Theory]
    [MemberData(nameof(LocalEntryCases))]
    public void LocalEntryBehavior(string test) => InspectorNativeTestRunner.Run(compiler, test);

    public static IEnumerable<object[]> PublicationCases() => InspectorNativeTestRunner.Cases("test_native.NativePublicationTests");

    [Theory]
    [MemberData(nameof(PublicationCases))]
    public void PublicationConsumersStartWithPrivateColdProjects(string test) => InspectorNativeTestRunner.Run(compiler, test);

    [Fact]
    public void LocalRestoredSeedKeepsNativeIncrementalExtraction() => InspectorNativeTestRunner.Run(compiler,
        "test_native.NativeLocalReportTests");

    public static IEnumerable<object[]> ReportCases() => InspectorNativeTestRunner.Cases("test_native.NativeReportTests");

    [Theory]
    [MemberData(nameof(ReportCases))]
    public void ReportConsumersStartWithPrivateColdProjects(string test) => InspectorNativeTestRunner.Run(compiler, test);
}

internal static class InspectorNativeTestRunner
{
    internal static void Interrupt(System.Diagnostics.Process process)
    {
        TestProcessRunner.InterruptPythonFixture(process);
        if (process.ExitCode != 143)
            throw new InvalidOperationException("native fixture did not acknowledge settled interruption: " + process.ExitCode);
    }

    internal static IEnumerable<object[]> Cases(string selection)
    {
        if (OperatingSystem.IsWindows()) return [[selection]];
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", "test_native_support.py", "--list", selection],
            Path.Combine(root, "tools/lean-inspector/tests"), TestBudgets.ReportSupervisorHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        var names = JsonSerializer.Deserialize<string[]>(result.StandardOutput)!;
        Assert.NotEmpty(names);
        Assert.Equal(names.Length, names.Distinct(StringComparer.Ordinal).Count());
        return names.Select(name => new object[] { name });
    }

    internal static void Run(InspectorCompilerFixture compiler, string suite)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var clock = TimeProvider.System;
        Console.WriteLine("NATIVE_CASE " + JsonSerializer.Serialize(new { phase = "start", suite, utc = clock.GetUtcNow() }));
        var prepared = clock.GetTimestamp();
        var needsCompiler = suite.StartsWith("test_native.", StringComparison.Ordinal);
        string[] environment = needsCompiler
            ? [$"STRATALINT_NATIVE_COMPILER_SEED={compiler.Path}"] : [];
        Console.WriteLine("NATIVE_CASE " + JsonSerializer.Serialize(new { phase = "compiler-ready", suite,
            utc = clock.GetUtcNow(), elapsed_ms = clock.GetElapsedTime(prepared).TotalMilliseconds }));
        var executed = clock.GetTimestamp();
        var result = TestProcessRunner.Run("env",
            [.. environment, "STRATALINT_NATIVE_COMMAND_OBSERVATION=1", "python3", "-B", "test_native_support.py", "--run", suite],
            Path.Combine(root, "tools/lean-inspector/tests"), TestBudgets.ReportSupervisorHangGuard, 1024 * 1024,
            standardOutput: Console.OpenStandardOutput(), standardError: Console.OpenStandardError(),
            interruptBeforeKill: Interrupt);
        Console.WriteLine("NATIVE_CASE " + JsonSerializer.Serialize(new { phase = "child-exit", suite,
            utc = clock.GetUtcNow(), elapsed_ms = clock.GetElapsedTime(executed).TotalMilliseconds, raw_exit = result.ExitCode,
            stdout_bytes = result.StandardOutput.Length, stderr_bytes = result.StandardError.Length }));
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput)
            + Encoding.UTF8.GetString(result.StandardError));
    }

    internal static void WriteCommandObservations(byte[] output)
    {
        try
        {
            using var reader = new StringReader(Encoding.UTF8.GetString(output));
            while (reader.ReadLine() is { } line)
                if (line.StartsWith("NATIVE_COMMAND_OBSERVATION ", StringComparison.Ordinal))
                    Console.WriteLine(line);
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
        var result = TestProcessRunner.Run("env",
            ["STRATALINT_NATIVE_COMMAND_OBSERVATION=1", "python3", "-B", "test_native_support.py", "--stage", source.Path],
            System.IO.Path.Combine(root, "tools/lean-inspector/tests"),
            TestBudgets.ReportSupervisorHangGuard, 1024 * 1024,
            interruptBeforeKill: InspectorNativeTestRunner.Interrupt);
        InspectorNativeTestRunner.WriteCommandObservations(result.StandardOutput);
        InspectorNativeTestRunner.WriteCommandObservations(result.StandardError);
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
