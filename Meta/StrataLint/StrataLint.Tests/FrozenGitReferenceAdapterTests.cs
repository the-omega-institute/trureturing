using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class FrozenGitReferenceAdapterTests
{
    [Fact]
    public void FrozenGitReferenceAdapterValidatesTreeMembershipAndDescriptorSelector()
    {
        using var repository = new TemporaryDirectory();
        ReviewRegressionTests.RunGit(repository.Path, "init");
        ReviewRegressionTests.RunGit(repository.Path, "config", "user.email", "stratalint@example.invalid");
        ReviewRegressionTests.RunGit(repository.Path, "config", "user.name", "StrataLint Tests");
        var sourcePath = Path.Combine(repository.Path, "D5", "S0", "Carrier", "A.lean");
        Directory.CreateDirectory(Path.GetDirectoryName(sourcePath)!);
        File.WriteAllText(sourcePath, "theorem a : True := by trivial\n", new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(repository.Path, "lean-toolchain"),
            "leanprover/lean4:v4.31.0\n",
            new UTF8Encoding(false));
        File.WriteAllText(Path.Combine(repository.Path, "lake-manifest.json"), "{}\n", new UTF8Encoding(false));
        ReviewRegressionTests.RunGit(repository.Path, "add", ".");
        ReviewRegressionTests.RunGit(repository.Path, "commit", "-m", "frozen reference fixture");
        var commit = ReviewRegressionTests.RunGit(repository.Path, "rev-parse", "HEAD").Trim();
        var tree = ReviewRegressionTests.RunGit(repository.Path, "rev-parse", "HEAD^{tree}").Trim();
        var source = ReviewRegressionTests.RunGit(repository.Path, "rev-parse", "HEAD:D5/S0/Carrier/A.lean").Trim();
        var toolchain = ReviewRegressionTests.RunGit(repository.Path, "rev-parse", "HEAD:lean-toolchain").Trim();
        var manifest = ReviewRegressionTests.RunGit(repository.Path, "rev-parse", "HEAD:lake-manifest.json").Trim();
        var input = new FrozenLedgerInput(
            "git-sha1:" + commit,
            "git-sha1:" + tree,
            "git-sha1:" + source,
            "D5/S0/Carrier/A.lean",
            "repository-snapshot-v1",
            new[] { "git-sha1:" + manifest, "git-sha1:" + toolchain }
                .Order(StringComparer.Ordinal)
                .ToImmutableArray());
        var gateway = new GitRepositoryGateway(repository.Path);

        var capability = gateway.ValidateFrozenReferences(FrozenLedgerReferenceSet.Create(
            ImmutableArray.Create(input),
            ImmutableArray<string>.Empty));

        Assert.Empty(typeof(TrustedFrozenGitReferences).GetConstructors(
            System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.Public));
        Assert.NotNull(capability);
        var forged = input with { DescriptorBlobOid = "git-sha1:" + toolchain };
        Assert.Throws<InvalidOperationException>(() => gateway.ValidateFrozenReferences(
            FrozenLedgerReferenceSet.Create(
                ImmutableArray.Create(forged),
                ImmutableArray<string>.Empty)));
    }
}
