using System.Diagnostics;
using System.Text;

namespace StrataLint.Scribe.Tests;

public sealed class DerivedConflictClassifierTests
{
    public static TheoryData<string> TrustRootPaths => new()
    {
        "Meta/StrataLint/" + "TOWER.yaml",
        "Meta/StrataLint/Golden/" + "c0-inaugural-conservative-certificate.json",
    };

    [Fact]
    public void ClassifierEqualsFileMapGeneratedPaths()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = FindRepositoryRoot();
        var manifest = FileMapLoader.LoadRepository(root);
        var tracked = Run(root, "git", ["ls-files"]);
        var paths = Lines(tracked.StandardOutput);
        var expected = paths
            .Where(path => manifest.Match(path) is [{ Kind: FileMapKind.Generated }])
            .ToHashSet(StringComparer.Ordinal);

        var actual = RunClassifier(root, Path.Combine(root, "Meta", "FILEMAP.toml"), paths);

        Assert.Equal(expected.Order(StringComparer.Ordinal), actual.Order(StringComparer.Ordinal));
    }

    [Theory]
    [MemberData(nameof(TrustRootPaths))]
    public void ClassifierExcludesProgramAndLedgerTrustRoots(string path)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = FindRepositoryRoot();

        Assert.Empty(RunClassifier(root, Path.Combine(root, "Meta", "FILEMAP.toml"), [path]));
    }

    [Fact]
    public void ClassifierFollowsNewFileMapKindsWithoutScriptEdits()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = FindRepositoryRoot();
        var fileMap = Path.Combine(Path.GetTempPath(), $"filemap-{Guid.NewGuid():N}.toml");
        try
        {
            File.WriteAllText(fileMap, SyntheticFileMap + "\n", new UTF8Encoding(false));
            _ = FileMapLoader.Parse(File.ReadAllBytes(fileMap), fileMap);

            var actual = RunClassifier(root, fileMap,
                ["Synthetic/generated/new.md", "Synthetic/ledger/root.json", "Synthetic/program/tool.sh"]);

            Assert.Equal(["Synthetic/generated/new.md"], actual);
        }
        finally
        {
            File.Delete(fileMap);
        }
    }

    private static string[] RunClassifier(string root, string fileMap, string[] paths)
    {
        var probe = """
            set -euo pipefail
            ROOT="$1"
            PR_SHEPHERD_FILEMAP_PATH="$2"
            source "$ROOT/Meta/StrataLint/scripts/shepherd/pr-shepherd-actions.sh"
            shift 2
            for path in "$@"; do
              if is_derived_conflict "$path"; then printf '%s\n' "$path"; fi
            done
            """;
        var result = Run(root, "/bin/bash",
            ["-c", probe, "derived-classifier", root, fileMap, .. paths]);
        return Lines(result.StandardOutput);
    }

    private static ProcessResult Run(string root, string fileName, string[] arguments)
    {
        var start = new ProcessStartInfo(fileName)
        {
            WorkingDirectory = root,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
        };
        foreach (var argument in arguments) start.ArgumentList.Add(argument);
        using var process = Process.Start(start) ?? throw new InvalidOperationException("process did not start");
        var standardOutput = process.StandardOutput.ReadToEnd();
        var standardError = process.StandardError.ReadToEnd();
        process.WaitForExit();
        Assert.True(process.ExitCode == 0, $"exit={process.ExitCode}\n{standardError}");
        return new ProcessResult(standardOutput);
    }

    private static string[] Lines(string text) =>
        text.Split('\n', StringSplitOptions.RemoveEmptyEntries);

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "CLAUDE.md"))) return current.FullName;
        }
        throw new DirectoryNotFoundException("Could not locate repository root.");
    }

    private sealed record ProcessResult(string StandardOutput);

    private const string SyntheticFileMap = """
        schema_version = 2

        [residence_policy]
        case_id = "SYNTHETIC"
        desired = "none"
        known_violation_count = 0
        status = "closed"

        [[files]]
        pattern = "Synthetic/generated/**"
        kind = "generated"
        produced_by = "SyntheticEmitter"
        consumed_by = ["reader"]
        verified_by = ["SyntheticEmitter"]
        authority = "synthetic"
        artifact_id = "none"
        runtime_disposition = "committed-source"

        [[files]]
        pattern = "Synthetic/ledger/**"
        kind = "ledger"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = ["synthetic"]
        authority = "self"
        artifact_id = "none"
        runtime_disposition = "committed-ledger"

        [[files]]
        pattern = "Synthetic/program/**"
        kind = "program"
        produced_by = "none"
        consumed_by = ["automation"]
        verified_by = ["synthetic"]
        authority = "self"
        artifact_id = "none"
        runtime_disposition = "committed-source"
        """;
}
