using System.Text;
using System.Security.Cryptography;

namespace StrataLint.Tests;

public sealed class LeanReportInputScriptTests
{
    internal const string CompatibilityPath = "Meta/lean-report.toml";
    internal const string SourcePatterns = "source_patterns = [\"Trureturing.lean\", \"D5/**/*.lean\"]\n";

    internal static void InstallReportConfiguration(string root)
    {
        Directory.CreateDirectory(Path.Combine(root, "Meta"));
        File.WriteAllText(Path.Combine(root, CompatibilityPath), "compatibility_version = 1\n" + SourcePatterns);
    }

    [Fact]
    public void CompatibilityVersionBumpChangesTokenAndRejectsOldReport()
    {
        using var fixture = new ProducerInputFixture();
        var before = fixture.Address();
        fixture.Plan(before, before);
        Assert.Equal(0, fixture.VerifySeed().ExitCode);

        fixture.Write("Meta/lean-report.toml", "compatibility_version = 2\nsource_patterns = [\"Trureturing.lean\", \"D5/**/*.lean\"]\n");
        var after = fixture.Address();

        Assert.NotEqual(before[0], after[0]);
        Assert.NotEqual(before[1], after[1]);
        Assert.Equal(before[2..], after[2..]);
        Assert.Equal(2, fixture.VerifySeed().ExitCode);
    }

    [Theory]
    [InlineData("repository")]
    [InlineData("repository[cache]")]
    public void FixedVersionInspectorEditsPreserveReportReuse(string repositoryName)
    {
        using var fixture = new ProducerInputFixture(repositoryName);
        const string judgeSource = "tools/lean-inspector/LeanInformationAudit/Nested/ProofBuilder.lean";
        const string unrelated = "tools/lean-inspector/LeanInformationAudit/README.md";
        fixture.Write(judgeSource, "def judgeFixture : True := by trivial\n");
        fixture.Write(unrelated, "fixture documentation\n");
        fixture.RegisterScripts(judgeSource);
        var before = fixture.Address();
        fixture.Plan(before, before);

        fixture.Append(unrelated, "x");
        Assert.Equal(before, fixture.Address());
        Assert.Empty(fixture.Plan(before, fixture.Address())["recheck"]!.AsArray());

        fixture.Append(judgeSource, "x");
        var after = fixture.Address();
        Assert.Equal(before, after);
        Assert.Empty(fixture.Plan(before, after)["recheck"]!.AsArray());
        Assert.Equal(0, fixture.VerifySeed().ExitCode);
    }

    [Fact]
    public void ProducerClosureFollowsRegisteredDependencies()
    {
        using var fixture = new ProducerInputFixture();
        var before = fixture.Address();
        fixture.Write(".github/workflows/unrelated.yml", "not a workflow");
        fixture.Write("tools/StrataLint.Cli/Unused.cs", "not registered");
        Assert.Equal(before, fixture.Address());
        const string dependency = "tools/lean-inspector/fixture_dependency.py";
        fixture.Write(dependency, "SEMANTIC_VALUE = 1\n");
        fixture.RegisterScripts(dependency);
        Assert.Contains(dependency, Encoding.UTF8.GetString(fixture.Run("producer-paths").StandardOutput));
        fixture.Write(dependency, "SEMANTIC_VALUE = 2\n");
        Assert.Equal(before, fixture.Address());
        fixture.Remove(dependency);
        var rejected = fixture.Run("producer-paths");
        Assert.Equal(2, rejected.ExitCode);
        Assert.Contains(dependency, Encoding.UTF8.GetString(rejected.StandardError));
    }

    [Fact]
    public void MetadataAndSemanticInputsHaveDistinctBehavior()
    {
        using var fixture = new ProducerInputFixture();
        var before = fixture.Address();
        fixture.Plan(before, before);
        Assert.Equal(0, fixture.VerifySeed().ExitCode);
        fixture.Write("lakefile.toml", "name = \"renamed\"\nkeywords = [\"metadata\"]\n");
        Assert.Equal(0, fixture.VerifySeed().ExitCode);
        Assert.Empty(fixture.Plan(before, fixture.Address())["recheck"]!.AsArray());
        fixture.Append(ProducerInputFixture.FetcherPath, "# declared producer changed\n");
        Assert.Equal(0, fixture.VerifySeed().ExitCode);
        fixture.Write(ProducerInputFixture.FetcherPath, "#!/bin/bash\n");
        fixture.Append("D5/Probe.lean", "-- changed source\n");
        Assert.Equal(2, fixture.VerifySeed().ExitCode);
        fixture.Write("D5/Probe.lean", "def probe := 1\n");
        fixture.Write("lakefile.toml", "[leanOptions]\nmaxRecDepth = 2000\n");
        Assert.Equal(2, fixture.VerifySeed().ExitCode);
    }

    [Theory]
    [InlineData("tools/StrataLint.Cli/Fixture.cs")]
    [InlineData("tools/StrataLint.Engine/Fixture.cs")]
    [InlineData("tools/Trureturing.Truth/Fixture.cs")]
    [InlineData("producer.props")]
    [InlineData("tools/StrataLint.Scribe/Fixture.cs")]
    [InlineData("tools/lean-inspector/Inspector.lean")]
    [InlineData("tools/scripts/report/lean-report-input.sh")]
    public void FixedVersionImplementationEditsPreserveAddressAndVerification(string path)
    {
        using var fixture = new ProducerInputFixture();
        var before = fixture.Address();
        fixture.Plan(before, before);
        fixture.Append(path, "\n ");
        var after = fixture.Address();
        Assert.Equal(before, after);
        Assert.Empty(fixture.Plan(before, after)["recheck"]!.AsArray());
        Assert.Equal(0, fixture.VerifySeed().ExitCode);
    }

    [Theory]
    [InlineData(null)]
    [InlineData("")]
    [InlineData("compatibility_version = 0\n")]
    [InlineData("compatibility_version = -1\n")]
    [InlineData("compatibility_version = true\n")]
    [InlineData("compatibility_version = \"1\"\n")]
    [InlineData("compatibility_version = 1.0\n")]
    [InlineData("compatibility_version = 01\n")]
    [InlineData("compatibility_version = 1\ncompatibility_version = 2\n")]
    [InlineData("compatibility_version = 1\nunknown = 2\n")]
    public void InvalidCompatibilityVersionFailsSpecifically(string? version)
    {
        using var fixture = new ProducerInputFixture();
        var before = fixture.Address();
        fixture.Plan(before, before);
        if (version is null) fixture.Remove(CompatibilityPath);
        else fixture.Write(CompatibilityPath, version + SourcePatterns);

        foreach (var command in new[] { "address", "verify", "modules", "compatibility-token" })
        {
            var result = command == "verify" ? fixture.VerifySeed() : fixture.Run(command);
            Assert.Equal(2, result.ExitCode);
            Assert.Empty(result.StandardOutput);
            Assert.Contains("compatibility_version", Encoding.UTF8.GetString(result.StandardError));
            Assert.Contains(CompatibilityPath, Encoding.UTF8.GetString(result.StandardError));
        }
    }

    [Fact]
    public void ManifestFormattingDoesNotChangeCompatibilityOrAddress()
    {
        using var fixture = new ProducerInputFixture();
        var before = fixture.Address();
        fixture.Write(CompatibilityPath,
            "# developer comment\n  compatibility_version = 1  # unchanged\n\n" + SourcePatterns);
        Assert.Equal(before, fixture.Address());
    }

    [Fact]
    public void RetiredScribeSelectionRegistrationIsRejected()
    {
        using var fixture = new ProducerInputFixture();
        fixture.Append(CompatibilityPath, "scribe_check_inputs = [\"tools/Explicit/*.cs\"]\n");
        var result = fixture.Run("address");
        Assert.Equal(2, result.ExitCode);
        Assert.Empty(result.StandardOutput);
        Assert.Contains("scribe_check_inputs", Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("")]
    [InlineData("source_patterns = [\"../outside.lean\"]\n")]
    [InlineData("source_patterns = [\"Trureturing.lean\", \"D5/**/*.lean\", \"D5/Probe.lean\"]\n")]
    public void MissingOrConflictingSourceRegistrationFailsWithoutFallback(string sources)
    {
        using var fixture = new ProducerInputFixture();
        fixture.Write(CompatibilityPath, "compatibility_version = 1\n" + sources);
        var result = fixture.Run("address");
        Assert.Equal(2, result.ExitCode);
        Assert.Empty(result.StandardOutput);
        Assert.Contains("source_patterns", Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void ModulesAndReportSourcesUseTheSameRegisteredSelection()
    {
        using var fixture = new ProducerInputFixture();
        fixture.Write("D5/Nested/Second.lean", "def second : Nat := 2\n");
        fixture.Write("tools/lean-inspector/Unused/Probe.lean", "-- unused fixture\n");
        var result = fixture.Run("modules");
        Assert.Equal(0, result.ExitCode);
        Assert.Equal(new[] { "Trureturing\tTrureturing.lean", "D5.Nested.Second\tD5/Nested/Second.lean", "D5.Probe\tD5/Probe.lean" },
            Encoding.UTF8.GetString(result.StandardOutput).Split('\n', StringSplitOptions.RemoveEmptyEntries));
        var preimage = string.Concat(new[]
        {
            ("Trureturing.lean", "import D5.Probe\n"),
            ("D5/Nested/Second.lean", "def second : Nat := 2\n"),
            ("D5/Probe.lean", "def probe := 1\n"),
        }.Select(row => Hash(row.Item2) + "  " + row.Item1 + "\n"));
        Assert.Equal(Hash(preimage), fixture.Address()[2]);

        static string Hash(string value) => Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(value)));
    }

    [Fact]
    public void ActionsWritePolicyDoesNotInvalidateReportReuse()
    {
        using var fixture = new ProducerInputFixture();
        const string policyPath = "tools/scripts/worktree/lean_actions.py";
        foreach (var path in new[] { policyPath, "tools/scripts/worktree/lean_cache_release.py", "tools/scripts/worktree/cache_material.py" })
            fixture.Write(path, File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), path)));
        var before = fixture.Address();
        fixture.Plan(before, before);
        Assert.False(fixture.ActionsPolicy()["save_allowed"]!.GetValue<bool>());
        var original = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), policyPath));
        var changed = original.Replace("== \"refs/heads/dev\"",
            "in (\"refs/heads/dev\", \"refs/heads/feature-policy-probe\")", StringComparison.Ordinal);
        Assert.NotEqual(original, changed);
        fixture.Write(policyPath, changed);
        Assert.True(fixture.ActionsPolicy()["save_allowed"]!.GetValue<bool>());
        Assert.Equal(before, fixture.Address());
        Assert.Empty(fixture.Plan(before, fixture.Address())["recheck"]!.AsArray());
    }
}
