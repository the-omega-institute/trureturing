using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Trait("Category", "Script")]
public sealed class LeanReportPerModuleScriptTests
{
    private const string InspectorScript = "Meta/StrataLint/lean-inspector/inspect.sh";
    private const string InspectorSource = "Meta/StrataLint/lean-inspector/Inspector.lean";
    private const string InputScript = "Meta/StrataLint/scripts/report/lean-report-input.sh";

    [Fact]
    public void ProducerDefaultsToAllModulesAndAcceptsACanonicalSubset()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var root = FindRepositoryRoot();
        var repository = Path.Combine(temporary.Path, "repo");
        Directory.CreateDirectory(Path.Combine(repository, "D5"));
        Directory.CreateDirectory(Path.Combine(repository, "Meta", "StrataLint", "lean-inspector"));
        Directory.CreateDirectory(Path.Combine(repository, "Meta", "StrataLint", "scripts", "report"));
        Write(repository, "Trureturing.lean", "import D5.Probe\n");
        Write(repository, "D5/Probe.lean", "def probe : Nat := 1\n");
        foreach (var relative in new[] { InspectorScript, InspectorSource, InputScript })
        {
            File.Copy(Path.Combine(root, relative), Path.Combine(repository, relative));
        }
        var lake = Path.Combine(temporary.Path, "lake");
        File.WriteAllText(lake, "#!/usr/bin/env bash\nprintf '%s\\n' \"$*\" >> \"$STUB_LOG\"\nif [[ \"$*\" == *' --output '* ]]; then while [[ $# -gt 0 ]]; do [[ $1 == --output ]] && { printf '{\"modules\": [], \"schema\": \"stratalint-raw-lean-report-v1\"}\\n' > \"$2\"; break; }; shift; done; fi\n", new UTF8Encoding(false));
        File.SetUnixFileMode(lake, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var log = Path.Combine(temporary.Path, "lake.log");
        var output = Path.Combine(temporary.Path, "report.json");

        var full = Run("env", [$"LAKE_BIN={lake}", $"STUB_LOG={log}", Path.Combine(repository, InspectorScript), "--repository", repository, "--output", output], repository);
        Assert.Equal(0, full.ExitCode);
        var fullInspect = File.ReadAllLines(log).Single(static line => line.Contains(" --output ", StringComparison.Ordinal));
        Assert.Contains("Trureturing Trureturing.lean sha256:", fullInspect, StringComparison.Ordinal);
        Assert.Contains("D5.Probe D5/Probe.lean sha256:", fullInspect, StringComparison.Ordinal);

        File.Delete(log);
        var subset = Path.Combine(temporary.Path, "modules.txt");
        File.WriteAllText(subset, "D5.Probe\n", new UTF8Encoding(false));
        var partial = Run("env", [$"LAKE_BIN={lake}", $"STUB_LOG={log}", Path.Combine(repository, InspectorScript), "--repository", repository, "--output", output, "--modules-file", subset], repository);
        Assert.Equal(0, partial.ExitCode);
        var partialInspect = File.ReadAllLines(log).Single(static line => line.Contains(" --output ", StringComparison.Ordinal));
        Assert.DoesNotContain("Trureturing Trureturing.lean", partialInspect, StringComparison.Ordinal);
        Assert.Contains("D5.Probe D5/Probe.lean sha256:", partialInspect, StringComparison.Ordinal);
    }

    [Fact]
    public void ProducerDoesNotExecuteCandidateModuleEnumerator()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var root = FindRepositoryRoot();
        var repository = Path.Combine(temporary.Path, "repo");
        Directory.CreateDirectory(Path.Combine(repository, "D5"));
        Write(repository, "Trureturing.lean", "import D5.Probe\n");
        Write(repository, "D5/Probe.lean", "def probe : Nat := 1\n");
        var marker = Path.Combine(temporary.Path, "candidate-helper-ran");
        var poisoned = Path.Combine(repository, InputScript);
        Directory.CreateDirectory(Path.GetDirectoryName(poisoned)!);
        File.WriteAllText(
            poisoned,
            $"#!/usr/bin/env bash\ntouch '{marker}'\nprintf 'Trureturing\\tTrureturing.lean\\n'\n",
            new UTF8Encoding(false));
        File.SetUnixFileMode(poisoned, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var lake = Path.Combine(temporary.Path, "lake");
        File.WriteAllText(lake, "#!/usr/bin/env bash\nif [[ \"$*\" == *' --output '* ]]; then while [[ $# -gt 0 ]]; do [[ $1 == --output ]] && { printf '{\"modules\": [], \"schema\": \"stratalint-raw-lean-report-v1\"}\\n' > \"$2\"; break; }; shift; done; fi\n", new UTF8Encoding(false));
        File.SetUnixFileMode(lake, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);

        var result = Run("env", [$"LAKE_BIN={lake}", Path.Combine(root, InspectorScript), "--repository", repository, "--output", Path.Combine(temporary.Path, "report.json")], repository);

        Assert.Equal(0, result.ExitCode);
        Assert.False(File.Exists(marker), "producer executed the candidate-owned module enumerator");
    }

    [Fact]
    public void ReusedAndFreshEntriesAssembleByteIdenticallyToAFullReport()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var cached = Path.Combine(temporary.Path, "cached.json");
        var fresh = Path.Combine(temporary.Path, "fresh.json");
        var output = Path.Combine(temporary.Path, "output.json");
        var modulesFile = Path.Combine(temporary.Path, "modules.txt");
        Write(temporary.Path, "D5/Unicode.lean", "def term : Nat := 1\n");
        Write(temporary.Path, "Trureturing.lean", "import D5.Unicode\n");
        Assert.Equal(0, Run("git", ["init", "-q"], temporary.Path).ExitCode);
        Assert.Equal(0, Run("git", ["add", "D5/Unicode.lean", "Trureturing.lean"], temporary.Path).ExitCode);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create([
                RawRepositoryEntry.FromText("D5/Unicode.lean", "def term : Nat := 1\n"),
                RawRepositoryEntry.FromText("Trureturing.lean", "import D5.Unicode\n"),
            ]))).Snapshot;
        var unicodeDeclaration = new LeanDeclaration(
            "Golden.term𝒪φ",
            "declaration",
            "Nat ≤ Nat",
            ImmutableArray<string>.Empty);
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            ["D5/Unicode.lean"] = new([], [unicodeDeclaration]),
            ["Trureturing.lean"] = new(["D5.Unicode"], []),
        });
        var expected = RawLeanReportArtifact.Write(snapshot, report);
        using var document = JsonDocument.Parse(expected.AsSpan().ToArray());
        var modules = document.RootElement.GetProperty("modules").EnumerateArray().ToArray();
        File.WriteAllBytes(cached, PartialReport(modules[0]));
        File.WriteAllBytes(fresh, PartialReport(modules[1]));
        File.WriteAllText(modulesFile, "D5.Unicode\n", new UTF8Encoding(false));

        var result = LeanReportMergeCommand.Run([
            "--repository", temporary.Path,
            "--cached", cached,
            "--fresh", fresh,
            "--cached-modules-file", modulesFile,
            "--output", output,
        ]);

        Assert.True(result.Success, result.Error);
        Assert.Equal(expected.AsSpan().ToArray(), File.ReadAllBytes(output));
    }

    [Fact]
    public void FullCachedReportIgnoresUnselectedChangedAndDeletedModules()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var cached = Path.Combine(temporary.Path, "cached.json");
        var fresh = Path.Combine(temporary.Path, "fresh.json");
        var output = Path.Combine(temporary.Path, "output.json");
        var modulesFile = Path.Combine(temporary.Path, "modules.txt");
        const string unicodeSource = "def term : Nat := 1\n";
        const string changedSource = "def changed : Nat := 2\n";
        const string rootSource = "import D5.Changed\nimport D5.Unicode\n";
        Write(temporary.Path, "D5/Changed.lean", changedSource);
        Write(temporary.Path, "D5/Unicode.lean", unicodeSource);
        Write(temporary.Path, "Trureturing.lean", rootSource);
        Assert.Equal(0, Run("git", ["init", "-q"], temporary.Path).ExitCode);
        Assert.Equal(0, Run("git", ["add", "D5/Changed.lean", "D5/Unicode.lean", "Trureturing.lean"], temporary.Path).ExitCode);

        var currentSnapshot = DecodeSnapshot(
            ("D5/Changed.lean", changedSource),
            ("D5/Unicode.lean", unicodeSource),
            ("Trureturing.lean", rootSource));
        var oldSnapshot = DecodeSnapshot(
            ("D5/Changed.lean", "def changed : Nat := 1\n"),
            ("D5/Deleted.lean", "def deleted : Nat := 1\n"),
            ("D5/Unicode.lean", unicodeSource),
            ("Trureturing.lean", rootSource));
        var reused = new LeanFileReport([], [new LeanDeclaration("Golden.term", "declaration", "Nat", [])]);
        var expectedReport = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            ["D5/Changed.lean"] = new([], []),
            ["D5/Unicode.lean"] = reused,
            ["Trureturing.lean"] = new(["D5.Changed", "D5.Unicode"], []),
        });
        var cachedReport = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            ["D5/Changed.lean"] = new([], []),
            ["D5/Deleted.lean"] = new([], []),
            ["D5/Unicode.lean"] = reused,
            ["Trureturing.lean"] = new(["D5.Changed", "D5.Unicode"], []),
        });
        File.WriteAllBytes(cached, RawLeanReportArtifact.Write(oldSnapshot, cachedReport).AsSpan().ToArray());
        var fullCurrent = RawLeanReportArtifact.Write(currentSnapshot, expectedReport);
        using var currentDocument = JsonDocument.Parse(fullCurrent.AsSpan().ToArray());
        var currentModules = currentDocument.RootElement.GetProperty("modules").EnumerateArray().ToArray();
        File.WriteAllBytes(fresh, PartialReport(currentModules[0], currentModules[2]));
        File.WriteAllText(modulesFile, "D5.Unicode\n", new UTF8Encoding(false));

        var result = LeanReportMergeCommand.Run([
            "--repository", temporary.Path,
            "--cached", cached,
            "--fresh", fresh,
            "--cached-modules-file", modulesFile,
            "--output", output,
        ]);

        Assert.True(result.Success, result.Error);
        Assert.Equal(fullCurrent.AsSpan().ToArray(), File.ReadAllBytes(output));
    }

    private static byte[] PartialReport(params JsonElement[] modules) =>
        StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(new
        {
            modules,
            schema = RawLeanReportArtifact.Schema,
        })).AsSpan().ToArray();

    private static RepositorySnapshot DecodeSnapshot(params (string Path, string Contents)[] entries) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(entries.Select(static entry =>
                RawRepositoryEntry.FromText(entry.Path, entry.Contents))))).Snapshot;

    private static ProcessOutput Run(string command, IReadOnlyList<string> arguments, string cwd) =>
        BoundedProcessRunner.Run(command, arguments, cwd, TimeSpan.FromSeconds(30), 1024 * 1024);

    private static void Write(string root, string relative, string contents)
    {
        var path = Path.Combine(root, relative);
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllText(path, contents, new UTF8Encoding(false));
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory); current is not null; current = current.Parent)
            if (File.Exists(Path.Combine(current.FullName, "CLAUDE.md"))) return current.FullName;
        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}
