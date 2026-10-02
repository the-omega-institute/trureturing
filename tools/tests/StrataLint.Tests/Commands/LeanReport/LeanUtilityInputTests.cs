using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.EngineeringScope;

namespace StrataLint.Tests;

public sealed class LeanUtilityInputTests
{
    [Fact]
    public void ProducerUsesCanonicalUtilityParserToCreateStructuredObligations()
    {
        var fixture = UtilityAdmissionTestSupport.RefutationFixture();
        var repository = new FakeRepositoryGateway(RawChangeSet.Create([]),
            UtilityAdmissionTestSupport.Raw(fixture.Files), null);
        var console = new BufferedConsole();
        var exit = CliApplication.Run(["lean-utility-input"],
            new ProductionCliEnvironment("/repo", repository, new FakeLeanReportSource(null)), console);

        Assert.Equal(0, exit);
        using var json = JsonDocument.Parse(console.Output);
        var obligation = Assert.Single(json.RootElement.EnumerateArray());
        Assert.Equal(RuleFixture.RingPath, obligation.GetProperty("modulePath").GetString());
        Assert.Equal(UtilityAdmissionTestSupport.Claim, obligation.GetProperty("claimGid").GetString());
        Assert.Equal("D5.S0.Carrier.Ring", obligation.GetProperty("claimModule").GetString());
        Assert.Equal("proposed_law", obligation.GetProperty("claimSelector").GetString());
        Assert.Equal("refuted_law", obligation.GetProperty("resultSelector").GetString());
        Assert.Equal(RuleFixture.RingPath, obligation.GetProperty("claimSourcePath").GetString());
        Assert.Equal("sha256:" + Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(
            System.Text.Encoding.UTF8.GetBytes(fixture.Files[RuleFixture.RingPath]))),
            obligation.GetProperty("claimSourceSha256").GetString());
    }

    [Fact]
    public void CurrentUtilityInputTracksClaimEditsAndUntrackedModulesWithoutReadingUnrelatedBodies()
    {
        using var repository = new TemporaryDirectory();
        TestGit.Run(repository.Path, "init");
        const string claimPath = "D5/S0/Carrier/Claim.lean";
        var source = UtilityAdmissionTestSupport.RefutationFixture().Files[RuleFixture.RingPath]
            .Replace(UtilityAdmissionTestSupport.Claim, "D5/S0/Carrier/Claim.proposed_law", StringComparison.Ordinal);
        Write(RuleFixture.RingPath, source);
        Write(claimPath, "def proposed_law : Prop := False\n");
        Write("docs/unrelated.md", "unrelated reference text\n");
        TestGit.Run(repository.Path, "add", ".");
        var full = LeanUtilityInputCommand.Run(() => GitRepositorySnapshotReader.ReadCurrent(repository.Path), []);
        Assert.Equal(0, full.ExitCode);
        var first = LeanUtilityInputCommand.Run(repository.Path, []);
        Assert.Equal(full, first);

        // This body is not an input to utility obligations. A full snapshot would
        // fail decoding it; the native producer must never read or decode it.
        File.WriteAllBytes(Path.Combine(repository.Path, "docs/unrelated.md"), [0xff]);
        Assert.Equal(first, LeanUtilityInputCommand.Run(repository.Path, []));
        Write(claimPath, "def proposed_law : Prop := True\n");
        const string untracked = "D5/S0/Carrier/Untracked.lean";
        Write(untracked, source);
        var current = LeanUtilityInputCommand.Run(repository.Path, []);
        Assert.Equal(0, current.ExitCode);
        using var json = JsonDocument.Parse(current.Output);
        var obligations = json.RootElement.EnumerateArray().ToArray();
        Assert.Equal(new[] { RuleFixture.RingPath, untracked },
            obligations.Select(item => item.GetProperty("modulePath").GetString()));
        var expectedHash = "sha256:" + Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(
            File.ReadAllBytes(Path.Combine(repository.Path, claimPath))));
        Assert.All(obligations, item => Assert.Equal(expectedHash, item.GetProperty("claimSourceSha256").GetString()));
        Assert.DoesNotContain(expectedHash, first.Output, StringComparison.Ordinal);

        File.Delete(Path.Combine(repository.Path, claimPath));
        var missing = LeanUtilityInputCommand.Run(repository.Path, []);
        Assert.Equal(2, missing.ExitCode);
        Assert.Contains("Refutation claim source is absent", missing.Error, StringComparison.Ordinal);

        void Write(string path, string text)
        {
            var fullPath = Path.Combine(repository.Path, path);
            Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
            File.WriteAllText(fullPath, text);
        }
    }

    [Fact]
    public void CurrentUtilityInputEnumeratesOnlyManagedLeanAndPolicyPaths()
    {
        using var repository = new TemporaryDirectory();
        TestGit.Run(repository.Path, "init");
        foreach (var (path, text) in UtilityAdmissionTestSupport.RefutationFixture().Files)
        {
            var fullPath = Path.Combine(repository.Path, path);
            Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
            File.WriteAllText(fullPath, text);
        }
        TestGit.Run(repository.Path, "add", ".");
        var expected = LeanUtilityInputCommand.Run(repository.Path, []);
        Assert.Equal(0, expected.ExitCode);

        // An unsupported entry outside D5 is not an input; the producer must not enumerate it.
        TestGit.Run(repository.Path, "update-index", "--add", "--cacheinfo",
            "160000,1111111111111111111111111111111111111111,vendor/submodule");
        Assert.Equal(expected, LeanUtilityInputCommand.Run(repository.Path, []));

        // Inside the scope, an undeclared symlink still fails closed.
        File.CreateSymbolicLink(Path.Combine(repository.Path, "D5/Alias.lean"), "S0/Carrier/Ring.lean");
        var linked = LeanUtilityInputCommand.Run(repository.Path, []);
        Assert.Equal(2, linked.ExitCode);
        Assert.Contains("FILEMAP", linked.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void CurrentUtilityInputStillRejectsMalformedManagedSource()
    {
        using var repository = new TemporaryDirectory();
        TestGit.Run(repository.Path, "init");
        var path = Path.Combine(repository.Path, RuleFixture.RingPath);
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllBytes(path, [0xff]);
        var result = LeanUtilityInputCommand.Run(repository.Path, []);
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("strict UTF-8", result.Error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("none")]
    [InlineData("kind=certified-instance; basis=terminal=gid:D5/S0/Carrier/Ring.fixed_sum")]
    [InlineData("kind=certified-instance; basis=refutes=gid:D5/S0/Carrier/Ring.proposed_law")]
    [InlineData("kind=certified-instance; basis=refutes=gid:D5/S0/Carrier/Ring.proposed_law; claim=D5/S0/Carrier/Ring.proposed_law; result=D5/S0/Carrier/Ring.refuted_law")]
    public void NonObligationsDoNotProduceInventedEvidence(string utility)
    {
        var fixture = UtilityAdmissionTestSupport.InstanceFixture(utility);
        var repository = new FakeRepositoryGateway(RawChangeSet.Create([]),
            UtilityAdmissionTestSupport.Raw(fixture.Files), null);
        var console = new BufferedConsole();
        Assert.Equal(0, CliApplication.Run(["lean-utility-input"],
            new ProductionCliEnvironment("/repo", repository, new FakeLeanReportSource(null)), console));
        Assert.Equal("[]", console.Output.Trim());
    }
}
