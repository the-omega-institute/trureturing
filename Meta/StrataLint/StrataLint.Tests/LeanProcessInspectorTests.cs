using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LeanProcessInspectorTests
{
    private const string Lakefile = """
        name = "snapshot_probe"
        version = "0.1.0"
        defaultTargets = ["Trureturing"]

        [[lean_lib]]
        name = "Trureturing"
        """;

    [Fact]
    public void InspectorBuildsAndReadsTheProvidedSnapshotInsteadOfCandidateDiskState()
    {
        using var repository = new TemporaryDirectory();
        File.WriteAllText(Path.Combine(repository.Path, "lakefile.toml"), Lakefile + "\n");
        File.WriteAllText(Path.Combine(repository.Path, "lean-toolchain"), "leanprover/lean4:v4.31.0\n");
        File.WriteAllText(Path.Combine(repository.Path, "Trureturing.lean"), "def diskOnly : Nat := 1\n");
        var build = BoundedProcessRunner.Run(
            "lake",
            new[] { "build" },
            repository.Path,
            TimeSpan.FromSeconds(120),
            4 * 1024 * 1024);
        Assert.Equal(0, build.ExitCode);
        var raw = RawRepositorySnapshot.Create(new[]
        {
            RawRepositoryEntry.FromText("lakefile.toml", Lakefile + "\n"),
            RawRepositoryEntry.FromText("lean-toolchain", "leanprover/lean4:v4.31.0\n"),
            RawRepositoryEntry.FromText("Trureturing.lean", "axiom snapshotOnly : False\n"),
        });
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;

        var report = new LeanProcessInspector(repository.Path).Inspect(snapshot);

        var file = report.Files.Single(static item => item.Key.Value == "Trureturing.lean").Value;
        Assert.Contains(file.Declarations, static item => item.Name == "snapshotOnly" && item.Kind == "axiom");
        Assert.DoesNotContain(file.Declarations, static item => item.Name == "diskOnly");
    }
}
