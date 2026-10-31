using System.Text;
using StrataLint.Cli;

namespace StrataLint.CliIntegration.Tests;

public sealed class ArtifactCapacityCiTests
{
    public static TheoryData<string> CountedPaths => new()
    {
        "CLAUDE.md",
        "Blueprint/D5/S0/Carrier/Fixture.scribe.cs",
        "Problems/fixture.md",
        "README.md",
        "docs/reports/fixture.md",
        "tools/TestSupport/StrataLint.RuleTestSupport/Fixture.cs",
        "Evidence/D5/fixture.txt",
        "docs/VISION.md",
        "docs/assets/inquiry-cycle.svg",
        "docs/develop/spec/lean_single_compile_intrinsic_information_escape_theory_and_spec.md",
        "docs/develop/spec/trureturing_engineering_optimization_v1.md",
        "tools/lean-inspector/README.md",
        "tools/scripts/agent/openproblem/README.md",
        "tools/scripts/agent/openproblem/SCREENED-OUT-fixture.md",
        "tools/scripts/agent/prime_slabs/CPU.md",
    };

    [Theory]
    [MemberData(nameof(CountedPaths))]
    public void ProductionSelectionAndSourceRejectOversizedArtifactsWithSl003(string path)
    {
        using var fixture = new CiFixture();
        fixture.Write(path, "baseline\n");
        fixture.Commit();
        foreach (var lines in new[] { 1001, 1000 })
        {
            fixture.Write(path, new string('\n', lines));
            var result = fixture.Source();
            var output = Encoding.UTF8.GetString(result.StandardOutput);
            Assert.True(result.ExitCode == (lines > 1000 ? 1 : 0),
                output + Encoding.UTF8.GetString(result.StandardError));
            Assert.Contains("--artifact-capacity", output, StringComparison.Ordinal);
            if (lines > 1000)
            {
                Assert.Contains("SL-003", output, StringComparison.Ordinal);
                Assert.Contains(path, output, StringComparison.Ordinal);
                Assert.Contains("1001 lines (hard limit 1000)", output, StringComparison.Ordinal);
            }
            Assert.False(Directory.Exists(Path.Combine(fixture.Root, ".lake")));
        }
    }

    [Theory]
    [InlineData("lake-manifest.json")]
    [InlineData("Golden/Projection/fixture.json")]
    [InlineData("Blueprint/D5/S0/Carrier/Fixture.md")]
    [InlineData("Library/notes/fixture.md")]
    [InlineData("docs/develop/theory/fixture.md")]
    public void ProductionCapacityPathKeepsCanonicalExemptions(string path)
    {
        using var fixture = new CiFixture();
        fixture.Write(path, new string('\n', 1001));
        var result = fixture.Source();
        Assert.Equal(0, result.ExitCode);
        Assert.Contains("--artifact-capacity", Encoding.UTF8.GetString(result.StandardOutput), StringComparison.Ordinal);
    }

    [Fact]
    public void ArtifactOnlyModeReadsChangedBodiesAndIgnoresUntouchedPressure()
    {
        using var fixture = new CiFixture();
        fixture.Write("README.md", new string('\n', 1001));
        fixture.Commit();
        fixture.Write("docs/reports/changed.md", new string('\n', 1000));
        var result = fixture.Source();
        Assert.Equal(0, result.ExitCode);
        // The narrow mode must not accidentally execute path policy or full current.
        Assert.DoesNotContain("SL-015", Encoding.UTF8.GetString(result.StandardOutput), StringComparison.Ordinal);
    }

    private sealed class CiFixture : IDisposable
    {
        private readonly TemporaryDirectory directory = new();
        private string baseline = "";
        internal string Root => directory.Path;

        internal CiFixture()
        {
            // Only fixture inputs are copied; production selection and execution are imported directly.
            foreach (var (path, text) in new RuleFixture().Files) Write(path, text);
            foreach (var path in new[] { "Meta/FILEMAP.toml", "Meta/FILEMAP.docs.reports.toml", "Meta/domains.yaml" })
                Write(path, File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), path)));
            Git("init", "-q");
            Commit();
        }

        internal void Write(string path, string text)
        {
            var destination = Path.Combine(Root, path);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.WriteAllText(destination, text);
        }

        internal void Commit()
        {
            Git("add", ".");
            Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "fixture");
            baseline = Git("rev-parse", "HEAD");
        }

        internal StrataLint.Runtime.ProcessOutput Source()
        {
            var repo = TestRepositoryLayout.FindRoot();
            var script = """
                import json, sys
                from pathlib import Path
                sys.path.insert(0, sys.argv[1] + '/tools/scripts/workflow')
                import ci_contract as contract
                import ci_checks as checks
                data, _ = contract.load(Path(sys.argv[1]))
                paths = contract.changed_paths(Path.cwd(), sys.argv[3])
                plan = contract.selection(data, paths, 'pull-request')
                print('PLAN ' + json.dumps(plan), flush=True)
                checks.CLI = sys.argv[2]
                changed = Path(sys.argv[4])
                contract.write_paths(changed, paths)
                raise SystemExit(checks.with_budget(Path(sys.argv[5]),
                    lambda: checks.current_phase('source', data, plan, sys.argv[3], changed)))
                """;
            using var execution = new TemporaryDirectory();
            return TestProcessRunner.Run("python3", ["-c", script, repo,
                typeof(Program).Assembly.Location, baseline,
                Path.Combine(execution.Path, "changed"), Path.Combine(execution.Path, "budget")],
                Root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        }

        private string Git(params string[] args)
        {
            var result = TestProcessRunner.Run("git", args, Root, TestBudgets.ScriptProcessHangGuard, 64 * 1024);
            Assert.Equal(0, result.ExitCode);
            return Encoding.UTF8.GetString(result.StandardOutput).Trim();
        }

        public void Dispose() => directory.Dispose();
    }
}
