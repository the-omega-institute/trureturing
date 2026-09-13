using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;
using TemporaryFile = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

public sealed partial class DagLedgerMathlibReanchorWriterTests
{
    [Theory]
    [InlineData("absent_parentheses", false)]
    [InlineData("absent_proof", true)]
    public void RealPreparationBindsPinnedSourceAndWriterLoadsOffline(string afterName, bool accepted)
    {
        using var temporary = new TemporaryDirectory();
        var root = Path.Combine(temporary.Path, "candidate");
        var external = Path.Combine(root, ".lake/packages/mathlib");
        var before = QLoad("registered_g");
        var after = QLoad(afterName, 'b');
        var externalPath = "ProbeExternal/Equality.lean";
        Write(external, externalPath, before.Snapshot.Files[RepoPath.CreateKnown(externalPath)].Text);
        Git(external, "init", "--quiet");
        Git(external, "add", ".");
        Commit(external);
        var oldPin = Git(external, "rev-parse", "HEAD").Trim();
        Write(external, externalPath, after.Snapshot.Files[RepoPath.CreateKnown(externalPath)].Text);
        Git(external, "add", ".");
        Commit(external);
        var newPin = Git(external, "rev-parse", "HEAD").Trim();
        foreach (var file in before.Snapshot.Files.Values.Concat(EventFiles(before.Catalog)))
            Write(root, file.Path.Value, file.Text);
        foreach (var material in before.Catalog.ClosedNodes)
            Assert.True(FrozenStateWriter.Write(root, material.RepoPath, material.StatementId));
        Write(root, ".gitignore", ".lake/\n");
        var inputs = new Dictionary<string, string> {
            ["lakefile.toml"] = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), "lakefile.toml")),
            ["tools/lean-inspector/SourceContext.lean"] = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(),
                "tools/lean-inspector/SourceContext.lean")),
            ["tools/lean-inspector/SourceOptions.lean"] = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(),
                "tools/lean-inspector/SourceOptions.lean")),
            ["tools/lean-inspector/source-context.py"] = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(),
                "tools/lean-inspector/source-context.py")),
            ["tools/lean-inspector/source-context.sh"] = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(),
                "tools/lean-inspector/source-context.sh")),
            ["tools/StrataLint.Cli/Commands/LeanSourceInputCommand.cs"] = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(),
                "tools/StrataLint.Cli/Commands/LeanSourceInputCommand.cs")),
            ["tools/StrataLint.Engine/Ledger/Admission/LeanSourceHeader.cs"] = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(),
                "tools/StrataLint.Engine/Ledger/Admission/LeanSourceHeader.cs")),
        };
        foreach (var (relative, source) in inputs) Write(root, relative, source);
        Write(root, "lake-manifest.json", SourceManifest(oldPin));
        Git(root, "init", "--quiet");
        Git(root, "add", ".");
        Commit(root);
        var baseline = Git(root, "rev-parse", "HEAD").Trim();
        foreach (var file in after.Snapshot.Files.Values.Where(f => f.Path.Value.EndsWith(".lean", StringComparison.Ordinal)))
            Write(root, file.Path.Value, file.Text);
        Write(root, "lake-manifest.json", SourceManifest(newPin));
        Git(root, "add", ".");
        var report = Path.Combine(temporary.Path, "current.json");
        File.Copy(after.ReportPath, report);
        File.Copy(after.ReportPath + ".materials.zip", report + ".materials.zip");
        QualifiedSourceContextFixture.EnsureCompilerCache();
        foreach (var source in new[] { "ProbeExternal/Equality.lean", "D5/S0/Carrier/Helper.lean" })
            _ = Run("compile", source);
        var first = Prepare("first");
        Assert.True(first.GetProperty("queries").GetInt32() > 0);
        Assert.Equal(!accepted, first.GetProperty("external_bytes").GetInt32() > 0);
        var bytes = TemporaryFile.ReadAllBytes(report + ".source-context.json");
        var second = Prepare("cached");
        Assert.Equal(0, second.GetProperty("queries").GetInt32());
        Assert.Equal(0, second.GetProperty("external_bytes").GetInt32());
        Assert.Equal(bytes, TemporaryFile.ReadAllBytes(report + ".source-context.json"));
        Directory.Delete(Path.Combine(root, ".lake"), recursive: true);
        Assert.Equal(0, Prepare("offline").GetProperty("queries").GetInt32());
        var ledger = Path.Combine(root, FrozenLedgerChangeClassifier.AcceptedRoot);
        var oldLedger = ReadLedgerDirectory(ledger);
        var result = DagLedgerMathlibReanchorWriter.Reanchor(root, new GitRepositoryGateway(root),
            new DagLedgerCommandPreparation.FileLeanReportSource(report), ["--base", baseline]);
        Assert.True(result.Success == accepted, result.Output + result.Error);
        if (!accepted)
        {
            Assert.Contains("PROPOSITION_SOURCE_LOCATION " + PathFor("A") + ":4:", result.Output, StringComparison.Ordinal);
            Assert.Equal(oldLedger, ReadLedgerDirectory(ledger));
        }
        else Assert.Contains("replacement_modules=1", result.Output, StringComparison.Ordinal);

        string SourceManifest(string pin) => JsonSerializer.Serialize(new { packages = new[] {
            new { name = "mathlib", type = "git", rev = pin, url = new Uri(external).AbsoluteUri } } });
        JsonElement Prepare(string mode)
        {
            var receipt = Run(mode).Split('\n')
                .Single(line => line.StartsWith("LEAN_SOURCE_CONTEXT ", StringComparison.Ordinal));
            output.WriteLine(afterName + " " + mode + " " + receipt);
            return JsonDocument.Parse(receipt["LEAN_SOURCE_CONTEXT ".Length..]).RootElement.Clone();
        }
        string Run(params string[] arguments)
        {
            var run = TestProcessRunner.Run("python3", ["-c", QualifiedSourceContextScripts.Preparation,
                TestRepositoryLayout.FindRoot(), root, report, baseline, .. arguments], TestRepositoryLayout.FindRoot(),
                BoundedProcessRunner.HangDetectionBudget, 4 * 1024 * 1024);
            Assert.True(run.ExitCode == 0, Encoding.UTF8.GetString(run.StandardOutput) + Encoding.UTF8.GetString(run.StandardError));
            return Encoding.UTF8.GetString(run.StandardOutput);
        }
        static void Write(string directory, string relative, string text)
        {
            var path = Path.Combine(directory, relative);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, text, new UTF8Encoding(false));
        }
        static string Git(string directory, params string[] arguments)
        {
            var result = TestProcessRunner.Run("git", arguments, directory, BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
            Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
            return Encoding.UTF8.GetString(result.StandardOutput);
        }
        static void Commit(string directory) => Git(directory, "-c", "user.name=Source Context Fixture", "-c",
            "user.email=source-context@example.invalid", "commit", "--quiet", "--no-gpg-sign", "-m", "source fixture");
    }
}
