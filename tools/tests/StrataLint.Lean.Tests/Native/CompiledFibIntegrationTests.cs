using System.Text;
using StrataLint.TestSupport;

namespace StrataLint.Lean.Tests;

public sealed class CompiledFibIntegrationTests
{
    [Theory]
    [InlineData("test_positive_source_native_macro_and_boundaries")]
    [InlineData("test_noop_and_unrelated_preserve_artifact_and_leaves")]
    [InlineData("test_private_transitive_source_and_layer_dependency_updates")]
    [InlineData("test_membership_removal_addition_and_eligibility")]
    [InlineData("test_invalid_native_bridge_fails_compilation")]
    [InlineData("test_native_reader_and_target_dependency_updates")]
    public void CompilerArtifactConsumer(string behavior)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        using var diagnostics = new TemporaryDirectory();
        string[] sources = ["Reg/Support/AuricFibCompiledSource.lean",
            "Reg/Support/AuricFibCompiledFixture.lean"];
        var ownsSources = sources.All(path => !File.Exists(Path.Combine(root, path)));
        try
        {
            var result = TestProcessRunner.Run("python3",
                ["-B", "tools/lean-inspector/tests/test_auric_fib_compiled.py",
                    "--diagnostics", diagnostics.Path, "CompiledFibIntegration." + behavior, "-v"], root,
                TestBudgets.ReportSupervisorHangGuard, 1024 * 1024,
                standardOutput: Console.OpenStandardOutput(), standardError: Console.OpenStandardError());
            Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput)
                + Encoding.UTF8.GetString(result.StandardError));
        }
        finally
        {
            WriteFinalDiagnostics(diagnostics.Path, behavior, Console.Out);
            // The ordinary supervisor kills the complete child tree on its
            // unchanged guard; remove only sources this invocation could own.
            if (ownsSources)
                foreach (var path in sources) File.Delete(Path.Combine(root, path));
        }
    }

    internal static void WriteFinalDiagnostics(string directory, string behavior, TextWriter output)
    {
        // This read runs after the unchanged supervisor outcome. It preserves
        // the final bytes even when the Python live tail was killed mid-poll.
        foreach (var channel in new[] { "phases", "stdout", "stderr", "stdout.cache", "stderr.cache" })
        {
            try
            {
                var path = Path.Combine(directory, channel);
                if (!File.Exists(path)) continue;
                using var file = new FileStream(path, FileMode.Open, FileAccess.Read, FileShare.ReadWrite);
                var bytes = file.Length;
                var retained = (int)Math.Min(bytes, 32 * 1024);
                file.Seek(bytes - retained, SeekOrigin.Begin);
                var tail = new byte[retained];
                file.ReadExactly(tail);
                output.WriteLine("FIB_COMPILED_FINAL_DIAGNOSTIC " + System.Text.Json.JsonSerializer.Serialize(new
                {
                    behavior, channel, total_bytes = bytes, retained_bytes = retained,
                    omitted_prefix_bytes = bytes - retained, text = Encoding.UTF8.GetString(tail),
                }));
                output.Flush();
            }
            catch (Exception error) when (error is IOException or UnauthorizedAccessException or ObjectDisposedException)
            {
                try { output.WriteLine("FIB_COMPILED_DIAGNOSTIC_UNAVAILABLE " + error.Message); }
                catch (Exception unavailable) when (unavailable is IOException or ObjectDisposedException) { }
            }
        }
    }
}

public sealed class CompiledFibObservationTests
{
    [Fact]
    public void ActualSupervisorGuardLeavesFinalChildEvidenceAndOriginalSkip()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        using var output = new StringWriter();
        var root = TestRepositoryLayout.FindRoot();
        var exception = Assert.Throws<SkipException>(() =>
        {
            try
            {
                TestProcessRunner.Run("python3", ["-B", "-c", """
                    import signal, sys
                    from pathlib import Path
                    root = Path(sys.argv[1])
                    (root / 'phases').write_text('{"phase":"native-inspect","boundary":"start"}\n')
                    (root / 'stderr').write_text('actual child output before guard')
                    signal.pause()
                    """, temporary.Path], root, TestBudgets.LocalProcessHangGuard, 1024 * 1024);
            }
            finally { CompiledFibIntegrationTests.WriteFinalDiagnostics(temporary.Path, "guard-fixture", output); }
        });
        Assert.StartsWith("infrastructure-hang-guard expired", exception.Message, StringComparison.Ordinal);
        Assert.Contains("native-inspect", output.ToString(), StringComparison.Ordinal);
        Assert.Contains("actual child output before guard", output.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void FinalGuardTailPreservesOutcomeAndReportsItsByteBoundary()
    {
        using var temporary = new TemporaryDirectory();
        File.WriteAllText(Path.Combine(temporary.Path, "phases"), "{\"phase\":\"native-inspect\",\"boundary\":\"start\"}\n");
        File.WriteAllText(Path.Combine(temporary.Path, "stderr"), new string('x', 40000) + "ENFILE without newline");
        using var output = new StringWriter();
        var expected = new TimeoutException("original 300 second guard");
        var actual = Record.Exception((Action)(() =>
        {
            try { throw expected; }
            finally { CompiledFibIntegrationTests.WriteFinalDiagnostics(temporary.Path, "selected-case", output); }
        }));
        Assert.Same(expected, actual);
        var lines = output.ToString().Split('\n', StringSplitOptions.RemoveEmptyEntries);
        Assert.Equal(2, lines.Length);
        using var tail = System.Text.Json.JsonDocument.Parse(lines[1].Split(' ', 2)[1]);
        Assert.Equal(32768, tail.RootElement.GetProperty("retained_bytes").GetInt32());
        Assert.True(tail.RootElement.GetProperty("omitted_prefix_bytes").GetInt64() > 0);
        Assert.EndsWith("ENFILE without newline", tail.RootElement.GetProperty("text").GetString(), StringComparison.Ordinal);
    }

    [Fact]
    public void CacheChildOutputIsLiveAndRawExitIsPreserved()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var phases = Path.Combine(temporary.Path, "phases");
        var stdout = Path.Combine(temporary.Path, "stdout");
        var stderr = Path.Combine(temporary.Path, "stderr");
        var observation = new StrataLint.EngineeringScope.LeanCacheCommandObservation(phases, stdout, stderr);
        var runner = new StrataLint.EngineeringScope.ProductionWorktreeProcessRunner(observation: observation);
        using var forwardedOut = new MemoryStream();
        using var forwardedError = new MemoryStream();
        var result = runner.Run("python3", ["-c", """
            import sys, time
            from pathlib import Path
            print('raw stdout', flush=True)
            print('raw stderr', file=sys.stderr, flush=True)
            while not all(Path(p).exists() and text in Path(p).read_text()
                          for p, text in zip(sys.argv[1:], ['raw stdout', 'raw stderr'])):
                time.sleep(0.01)
            sys.exit(37)
            """, stdout, stderr], temporary.Path, TestBudgets.ReportSupervisorHangGuard,
                observation.Output(forwardedOut), observation.Error(forwardedError));
        Assert.Equal(37, result.ExitCode);
        Assert.Equal("raw stdout\n", Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Equal("raw stderr\n", Encoding.UTF8.GetString(result.StandardError));
        Assert.Equal("raw stdout\n", File.ReadAllText(stdout));
        Assert.Equal("raw stderr\n", File.ReadAllText(stderr));
        Assert.Equal(result.StandardOutput, forwardedOut.ToArray());
        Assert.Equal(result.StandardError, forwardedError.ToArray());
        using var last = System.Text.Json.JsonDocument.Parse(File.ReadLines(phases).Last());
        Assert.Equal(37, last.RootElement.GetProperty("raw_exit").GetInt32());
        Assert.Equal("finish", last.RootElement.GetProperty("boundary").GetString());
    }

    [Fact]
    public void UnwritableDiagnosticsPreserveRawStreamsAndCancellation()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var blocked = Path.Combine(temporary.Path, "blocked");
        File.WriteAllText(blocked, "regular file");
        var observation = new StrataLint.EngineeringScope.LeanCacheCommandObservation(
            Path.Combine(blocked, "phases"), Path.Combine(blocked, "stdout"), Path.Combine(blocked, "stderr"));
        var runner = new StrataLint.EngineeringScope.ProductionWorktreeProcessRunner(observation: observation);
        var result = runner.Run("python3", ["-c",
            "import sys; print('raw stdout'); print('raw stderr', file=sys.stderr); sys.exit(41)"],
            temporary.Path, TestBudgets.ReportSupervisorHangGuard);
        Assert.Equal(41, result.ExitCode);
        Assert.Equal("raw stdout\n", Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Equal("raw stderr\n", Encoding.UTF8.GetString(result.StandardError));
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        var cancelled = new StrataLint.EngineeringScope.ProductionWorktreeProcessRunner(cancellation.Token, observation);
        Assert.Throws<OperationCanceledException>(() => cancelled.Run("python3", ["-c", "pass"],
            temporary.Path, TestBudgets.ReportSupervisorHangGuard));
    }

    [Fact]
    public void LiveDiagnosticTransportPreservesOriginalOutcomes()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", "tools/lean-inspector/tests/test_auric_fib_compiled.py", "CompiledFibObservationTests", "-v"],
            root, TestBudgets.ReportSupervisorHangGuard, 1024 * 1024,
            standardOutput: Console.OpenStandardOutput(), standardError: Console.OpenStandardError());
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput)
            + Encoding.UTF8.GetString(result.StandardError));
    }
}
