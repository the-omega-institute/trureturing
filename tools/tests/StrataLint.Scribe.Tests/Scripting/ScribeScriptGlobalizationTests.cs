using System.Diagnostics;
using System.Text.Json;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Xunit.Abstractions;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeScriptGlobalizationTests(ITestOutputHelper output)
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task BackendDataVersionIsStableAcrossProcesses(bool invariant)
    {
        using var root = new TemporaryRoot();
        var worker = CreateWorker(root);
        WriteDefinition(root, "System.StringComparison.Ordinal");
        var first = await Pack(root, worker, invariant, "first.zip");
        var second = await Pack(root, worker, invariant, "second.zip");
        Assert.True(first.Exit == 0, first.Output + first.Error);
        Assert.True(second.Exit == 0, second.Output + second.Error);
        var firstVersion = Assert.Single(first.Output.Split('\n'), line => line.StartsWith("backendDataVersion=", StringComparison.Ordinal));
        var secondVersion = Assert.Single(second.Output.Split('\n'), line => line.StartsWith("backendDataVersion=", StringComparison.Ordinal));
        Assert.Equal(firstVersion, secondVersion);
        Assert.Equal(firstVersion["backendDataVersion=".Length..].Trim(),
            ScribeResourcePack.Open(root.Resolve("first.zip")).Manifest.ExecutionEnvironment.GlobalizationBackendDataVersion);
        Assert.Equal(ScribeResourcePack.Open(root.Resolve("first.zip")).Manifest.ExecutionEnvironment,
            ScribeResourcePack.Open(root.Resolve("second.zip")).Manifest.ExecutionEnvironment);
        output.WriteLine($"invariant={invariant}; {firstVersion.Trim()}");
    }

    [Fact]
    public async Task OrdinalPacksMatchAcrossGlobalizationBackendsForFreshAndReuse()
    {
        using var root = new TemporaryRoot();
        var worker = CreateWorker(root);
        WriteDefinition(root, "System.StringComparison.Ordinal");
        var icu = await Pack(root, worker, false, "icu.zip");
        var invariant = await Pack(root, worker, true, "invariant.zip");
        var reused = await Pack(root, worker, true, "reused.zip", "icu.zip");
        Assert.True(icu.Exit == 0, icu.Output + icu.Error);
        Assert.True(invariant.Exit == 0, invariant.Output + invariant.Error);
        Assert.True(reused.Exit == 0, reused.Output + reused.Error);
        Assert.Contains("globalizationInvariant=False", icu.Output, StringComparison.Ordinal);
        Assert.Contains("globalizationInvariant=True", invariant.Output, StringComparison.Ordinal);
        output.WriteLine("icu: " + icu.Output.Trim());
        output.WriteLine("invariant: " + invariant.Output.Trim());
        output.WriteLine("reuse: " + reused.Output.Trim());
        Assert.Contains("executed=1 reused=0", icu.Output, StringComparison.Ordinal);
        Assert.Contains("executed=1 reused=0", invariant.Output, StringComparison.Ordinal);
        Assert.Contains("executed=1 reused=0", reused.Output, StringComparison.Ordinal);
        Assert.Contains("reuseSkipped=globalizationBackend", reused.Output, StringComparison.Ordinal);
        var expected = ScribeResourcePack.Open(root.Resolve("icu.zip")).Manifest.TotalSha256;
        Assert.Equal(expected, ScribeResourcePack.Open(root.Resolve("invariant.zip")).Manifest.TotalSha256);
        Assert.Equal(expected, ScribeResourcePack.Open(root.Resolve("reused.zip")).Manifest.TotalSha256);
        WriteDefinition(root, "(System.StringComparison)0");
        var rejectedIcu = await Pack(root, worker, false, "rejected-icu.zip");
        var rejectedInvariant = await Pack(root, worker, true, "rejected-invariant.zip", "icu.zip");
        Assert.Equal(1, rejectedIcu.Exit);
        Assert.Equal(1, rejectedInvariant.Exit);
        Assert.Contains("DisallowedSymbol", rejectedIcu.Error, StringComparison.Ordinal);
        Assert.Equal(rejectedIcu.Error, rejectedInvariant.Error);
        Assert.False(File.Exists(root.Resolve("rejected-icu.zip")));
        Assert.False(File.Exists(root.Resolve("rejected-invariant.zip")));
    }

    private static string CreateWorker(TemporaryRoot root)
    {
        const string source = """
            using System;
            using System.IO;
            using System.Reflection;
            using System.Runtime.CompilerServices;
            using StrataLint.Scribe;
            public static class Program
            {
                public static int Main(string[] args)
                {
                    AppDomain.CurrentDomain.AssemblyResolve += (_, eventArgs) =>
                    {
                        var name = new AssemblyName(eventArgs.Name).Name!;
                        var path = Path.Combine(args[0], (name.Contains("BannedApiAnalyzers") ? "Scripting/" : "") + name + ".dll");
                        return File.Exists(path) ? Assembly.LoadFrom(path) : null;
                    };
                    AppContext.TryGetSwitch("System.Globalization.Invariant", out var invariant);
                    Console.WriteLine("globalizationInvariant=" + invariant);
                    var version = System.Globalization.CultureInfo.InvariantCulture.CompareInfo.Version;
                    Console.WriteLine("backendDataVersion=" + version.FullVersion.ToString(System.Globalization.CultureInfo.InvariantCulture)
                        + ":" + version.SortId.ToString("D"));
                    return Run(args);
                }
                [MethodImpl(MethodImplOptions.NoInlining)]
                private static int Run(string[] args) => ScribeCli.Run(typeof(ScribeCli).Assembly,
                    args[2..], args[1], Console.Out, Console.Error);
            }
            """;
        var references = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")!).Split(Path.PathSeparator)
            .Append(typeof(ScribeCli).Assembly.Location).Distinct(StringComparer.Ordinal)
            .Select(path => MetadataReference.CreateFromFile(path));
        var compilation = CSharpCompilation.Create("GlobalizationWorker", [CSharpSyntaxTree.ParseText(source)],
            references, new CSharpCompilationOptions(OutputKind.ConsoleApplication));
        using var image = new MemoryStream();
        var emitted = compilation.Emit(image);
        Assert.True(emitted.Success, string.Join(Environment.NewLine, emitted.Diagnostics));
        var worker = root.Resolve("worker/GlobalizationWorker.dll");
        TemporaryFileSystem.File.WriteAllBytes(worker, image.ToArray());
        foreach (var file in Directory.EnumerateFiles(Path.Combine(AppContext.BaseDirectory, "Scripting")))
            TemporaryFileSystem.File.WriteAllBytes(root.Resolve("worker/Scripting/" + Path.GetFileName(file)), File.ReadAllBytes(file));
        return worker;
    }

    private static async Task<(int Exit, string Output, string Error)> Pack(TemporaryRoot root, string worker,
        bool invariant, string output, string? reuse = null)
    {
        TemporaryFileSystem.File.WriteAllText(root.Resolve("worker/GlobalizationWorker.runtimeconfig.json"),
            JsonSerializer.Serialize(new
            {
                runtimeOptions = new
                {
                    tfm = "net10.0", framework = new { name = "Microsoft.NETCore.App", version = "10.0.0" },
                    configProperties = new Dictionary<string, object> { ["System.Globalization.Invariant"] = invariant },
                },
            }));
        var start = new ProcessStartInfo("dotnet")
        {
            WorkingDirectory = root.Path, RedirectStandardOutput = true, RedirectStandardError = true,
        };
        foreach (var argument in new[] { worker, AppContext.BaseDirectory, root.Path, "resources", "pack", "--out", output })
            start.ArgumentList.Add(argument);
        if (reuse is not null)
        {
            start.ArgumentList.Add("--reuse-from");
            start.ArgumentList.Add(reuse);
        }
        using var process = Process.Start(start)!;
        var stdout = process.StandardOutput.ReadToEndAsync();
        var stderr = process.StandardError.ReadToEndAsync();
        using var deadline = new CancellationTokenSource(TestBudgets.WorkflowProcessHangGuard);
        try { await process.WaitForExitAsync(deadline.Token); }
        catch (OperationCanceledException)
        {
            if (!process.HasExited) process.Kill(entireProcessTree: true);
            throw;
        }
        return (process.ExitCode, await stdout, await stderr);
    }

    private static void WriteDefinition(TemporaryRoot root, string comparison)
    {
        TemporaryFileSystem.File.WriteAllText(root.Resolve("global.json"), "{}");
        TemporaryFileSystem.File.WriteAllText(root.Resolve("Blueprint/D5/S0/Test/Probe.scribe.cs"), $$"""
            using StrataLint.Scribe;
            using static StrataLint.Scribe.DefinitionDsl;
            internal sealed class Probe : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("digest",
                    H("Hel\0lo".IndexOf("\0", {{comparison}}).ToString(System.Globalization.CultureInfo.InvariantCulture)),
                    Blocks(Paragraph(Text("content")))));
            }
            """);
    }
}
