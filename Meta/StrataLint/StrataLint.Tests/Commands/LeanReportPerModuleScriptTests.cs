using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LeanReportPerModuleScriptTests
{
    private const string InspectorScript = "Meta/StrataLint/lean-inspector/inspect.sh";
    private const string MergeScript = "Meta/StrataLint/scripts/report/lean-report-merge.sh";

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
        foreach (var relative in new[] { InspectorScript, "Meta/StrataLint/lean-inspector/Inspector.lean", "Meta/StrataLint/scripts/report/lean-report-input.sh" })
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
    public void ReusedAndFreshEntriesAssembleByteIdenticallyToAFullReport()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var full = Path.Combine(temporary.Path, "full.json");
        var cached = Path.Combine(temporary.Path, "cached.json");
        var fresh = Path.Combine(temporary.Path, "fresh.json");
        var output = Path.Combine(temporary.Path, "output.json");
        var moduleA = "{\"declarations\": [], \"imports\": [], \"module\": \"A\", \"source_path\": \"A.lean\", \"source_sha256\": \"sha256:" + new string('a', 64) + "\"}";
        var moduleB = "{\"declarations\": [], \"imports\": [], \"module\": \"B\", \"source_path\": \"B.lean\", \"source_sha256\": \"sha256:" + new string('b', 64) + "\"}";
        File.WriteAllText(full, $"{{\"modules\": [{moduleA}, {moduleB}], \"schema\": \"stratalint-raw-lean-report-v1\"}}\n", new UTF8Encoding(false));
        File.WriteAllText(cached, $"{{\"modules\": [{moduleA}], \"schema\": \"stratalint-raw-lean-report-v1\"}}\n", new UTF8Encoding(false));
        File.WriteAllText(fresh, $"{{\"modules\": [{moduleB}], \"schema\": \"stratalint-raw-lean-report-v1\"}}\n", new UTF8Encoding(false));

        var result = Run("bash", [Path.Combine(FindRepositoryRoot(), MergeScript), "--cached", cached, "--fresh", fresh, "--output", output], temporary.Path);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(File.ReadAllBytes(full), File.ReadAllBytes(output));
    }

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
