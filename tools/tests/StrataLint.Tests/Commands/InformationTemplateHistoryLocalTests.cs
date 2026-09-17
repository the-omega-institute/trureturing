using StrataLint.Cli;
using StrataLint.Engine;
using File = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

public sealed class InformationTemplateHistoryLocalTests
{
    [Fact]
    public void explicit_seed_from_clean_head_supplies_writer_default_without_override()
    {
        using var fixture = new InformationTemplateHistoryFixture();
        var root = Path.Combine(fixture.Scratch.Path, "installed repository");
        Directory.CreateDirectory(root);
        string Git(params string[] args) => ReviewRegressionTests.RunGit(root, args).Trim();
        Git("init");
        Git("config", "user.email", "stratalint@example.invalid");
        Git("config", "user.name", "StrataLint Tests");
        foreach (var (path, text) in fixture.Historical.Where(p => p.Key != InformationTemplateDebtStore.ActivationPath))
        {
            Directory.CreateDirectory(Path.GetDirectoryName(Path.Combine(root, path))!);
            File.WriteAllText(Path.Combine(root, path), text);
        }
        Git("add", ".");
        Git("commit", "-m", "historical content");
        var seed = Git("rev-parse", "HEAD");
        foreach (var (path, text) in fixture.Candidate)
        {
            Directory.CreateDirectory(Path.GetDirectoryName(Path.Combine(root, path))!);
            File.WriteAllText(Path.Combine(root, path), text);
        }
        File.Delete(Path.Combine(root, "Meta/lean-report.toml"));
        File.WriteAllBytes(Path.Combine(root, InformationTemplateDebtStore.ActivationPath),
            InformationTemplateDebtStore.WriteActivation(new(seed, false)).ToArray());
        Git("add", "-A");
        Git("commit", "-m", "installed candidate producer");
        var head = Git("rev-parse", "HEAD");
        var gateway = new GitRepositoryGateway(root);
        var plan = InformationTemplateHistoryCommand.Run(root, gateway,
            ["plan", "--protected-base", head, "--purpose", "seed", "--output", fixture.Plan], fixture, TimeProvider.System);
        Assert.True(plan.Success, "[FAIL] explicit seed plan: " + plan.Error);
        var produced = InformationTemplateHistoryCommand.Run(root, gateway,
            ["produce", "--plan", fixture.Plan, "--revision", seed, "--work", fixture.Work,
                "--output", Path.Combine(root, ".lake/build/stratalint/information-template-history", seed),
                "--cache-root", Path.Combine(fixture.Scratch.Path, "cache")], fixture, TimeProvider.System);
        Assert.True(produced.Success, "[FAIL] seed default publication: " + produced.Error);
        var initialized = InformationTemplateDebtWriter.Run(root, gateway, ["initialize", "--protected-base", head]);
        Assert.True(initialized.Success, "[FAIL] seed default writer: " + initialized.Error);
        Assert.Empty(Git("status", "--porcelain"));
        Assert.Contains("history comparison would be vacuous", Assert.Throws<InvalidOperationException>(() => gateway.Prepare(head)).Message);
        // Scoped planning reads bytes only for activation. Even an unexpected,
        // untracked debt file must enter the exact HasRows population.
        File.WriteAllText(Path.Combine(root, InformationTemplateDebtStore.Root, "unexpected.txt"), "not JSON");
        var scoped = ((IInformationTemplateHistoryRepository)gateway).ReadPredicate(null);
        Assert.Contains(scoped.Entries, e => e.Path.EndsWith("unexpected.txt", StringComparison.Ordinal) && e.Bytes.IsEmpty && !e.IsTracked);
        var committed = ((IInformationTemplateHistoryRepository)gateway).ReadPredicate(head);
        Assert.Single(committed.Entries);
        Assert.False(committed.Entries[0].Bytes.IsEmpty);
    }

    [Fact]
    public void active_plan_supplies_both_revisions_and_validated_relocation_needs_no_producer()
    {
        using var fixture = new InformationTemplateHistoryFixture();
        fixture.Candidate[InformationTemplateDebtStore.ActivationPath] = DeclaredTemplateReviewTests.Text(
            InformationTemplateDebtStore.WriteActivation(new(fixture.Seed, true)));
        Assert.True(fixture.Command("plan", "--protected-base", fixture.Head, "--output", fixture.Plan).Success);
        foreach (var revision in new[] { fixture.Seed, fixture.Head })
        {
            var output = Path.Combine(fixture.Scratch.Path, "reports", "information-template-history", revision);
            var result = fixture.Command("produce", "--plan", fixture.Plan, "--revision", revision,
                "--work", Path.Combine(fixture.Scratch.Path, "work " + revision), "--output", output);
            Assert.True(result.Success, "[FAIL] active historical production: " + result.Error);
            Assert.True(fixture.Command("validate", "--plan", fixture.Plan, "--revision", revision, "--bundle", output,
                "--output", Path.Combine(fixture.Scratch.Path, "consumer", "information-template-history", revision)).Success);
        }
        Assert.Equal(2, fixture.Productions);
    }
}
