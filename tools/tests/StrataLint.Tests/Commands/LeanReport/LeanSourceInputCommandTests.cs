using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using TemporaryFile = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

public sealed class LeanSourceInputCommandTests
{
    [Theory]
    [InlineData(null)]
    [InlineData("{")]
    [InlineData("{\"schema\":\"lean-source-context/1\"}")]
    public void CanonicalUnusedSiblingVerifiesOfflineAndPreparationPublishesCompleteShape(string? sibling)
    {
        using var temporary = new TemporaryDirectory();
        var root = Path.Combine(temporary.Path, "repository");
        Directory.CreateDirectory(root);
        Git("init", "--quiet");
        File.WriteAllText(Path.Combine(root, "README.md"), "fixture baseline\n");
        Git("add", ".");
        Git("-c", "user.name=Source Fixture", "-c", "user.email=source@example.invalid", "commit", "--quiet",
            "--no-gpg-sign", "-m", "baseline");
        var baseline = Git("rev-parse", "HEAD").Trim();
        Directory.CreateDirectory(Path.Combine(root, "D5"));
        File.WriteAllText(Path.Combine(root, "D5/Anonymous.lean"), "import Init\nexample : True := by decide\n");
        Git("add", ".");
        var report = Path.Combine(temporary.Path, "no-declarations.json");
        if (sibling is not null) File.WriteAllText(report + ".source-context.json", sibling);
        Run("offline");
        Run("cached");
        using var result = JsonDocument.Parse(TemporaryFile.ReadAllBytes(report + ".source-context.json"));
        Assert.Equal(0, result.RootElement.GetProperty("files").GetArrayLength());
        Assert.Equal(0, result.RootElement.GetProperty("registrations").GetArrayLength());
        Assert.False(Directory.Exists(Path.Combine(root, ".lake")));

        void Run(string mode)
        {
            var run = TestProcessRunner.Run("python3", ["-c", QualifiedSourceContextScripts.Preparation,
                TestRepositoryLayout.FindRoot(), root, report, baseline, mode], TestRepositoryLayout.FindRoot(),
                BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
            Assert.True(run.ExitCode == 0, System.Text.Encoding.UTF8.GetString(run.StandardOutput)
                + System.Text.Encoding.UTF8.GetString(run.StandardError));
            Assert.Contains("\"compiler_modules\": 0", System.Text.Encoding.UTF8.GetString(run.StandardOutput), StringComparison.Ordinal);
        }
        string Git(params string[] arguments)
        {
            var run = TestProcessRunner.Run("git", arguments, root, BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
            Assert.True(run.ExitCode == 0, System.Text.Encoding.UTF8.GetString(run.StandardError));
            return System.Text.Encoding.UTF8.GetString(run.StandardOutput);
        }
    }

    [Theory]
    [InlineData("example : ')' =')' := by decide\n", 1)]
    [InlineData("example : True := by native_decide\n", 0)]
    [InlineData("example : True := by decide\n", 0)]
    public void SourceDemandIsIndependentOfDeclarationReport(string source, int requests)
    {
        const string path = "D5/S0/Carrier/Anonymous.lean";
        using var temporary = new TemporaryDirectory();
        var current = RawRepositorySnapshot.Create([RawRepositoryEntry.FromText(path, "import Init\n" + source)]);
        var baseline = RawRepositorySnapshot.Create([]);
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([path]), current, baseline);
        var result = LeanSourceInputCommand.Run(gateway,
            ["--base", new string('a', 40), "--report", Path.Combine(temporary.Path, "no-declarations.json")]);
        Assert.Equal(0, result.ExitCode);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal(requests, json.RootElement.GetProperty("requests").GetArrayLength());
        if (requests == 1)
        {
            var request = json.RootElement.GetProperty("requests")[0];
            Assert.Equal(path, request.GetProperty("path").GetString());
            Assert.Equal("current", request.GetProperty("side").GetString());
            Assert.Equal("commands", request.GetProperty("kind").GetString());
            Assert.Contains(source, request.GetProperty("source").GetString());
        }
    }
}
