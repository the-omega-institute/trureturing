using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.InformationTemplateDebtStoreTests;

namespace StrataLint.Tests;

public sealed class InformationTemplateDebtWriterTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void seed_initialization_accepts_clean_installed_head(bool active)
    {
        using var repository = new TemporaryDirectory();
        using var artifacts = new TemporaryDirectory();
        string Git(params string[] args) => ReviewRegressionTests.RunGit(repository.Path, args).Trim();
        Git("init");
        Git("config", "user.email", "stratalint@example.invalid");
        Git("config", "user.name", "StrataLint Tests");
        foreach (var (path, text) in DeclaredTemplateReviewTests.PolicyFiles())
        {
            var full = Path.Combine(repository.Path, path);
            Directory.CreateDirectory(Path.GetDirectoryName(full)!);
            File.WriteAllText(full, text);
        }
        Git("add", ".");
        Git("commit", "-m", "seed");
        var seed = Git("rev-parse", "HEAD");
        var activationPath = Path.Combine(repository.Path, InformationTemplateDebtStore.ActivationPath);
        Directory.CreateDirectory(Path.GetDirectoryName(activationPath)!);
        var activation = InformationTemplateDebtStore.WriteActivation(new(seed, active));
        File.WriteAllBytes(activationPath, activation.AsSpan());
        Git("add", ".");
        Git("commit", "-m", "installed mechanism");
        var head = Git("rev-parse", "HEAD");
        var gateway = new GitRepositoryGateway(repository.Path);
        Assert.Empty(Git("status", "--porcelain"));
        Assert.Contains("history comparison would be vacuous",
            Assert.Throws<InvalidOperationException>(() => gateway.Prepare(head)).Message);
        var report = Path.Combine(artifacts.Path, "seed-report.json");
        File.WriteAllBytes(report, Trureturing.Truth.StructuredCanonicalWriter.WriteJson(
            "{\"modules\":[],\"schema\":\"stratalint-raw-lean-report-v2\"}").AsSpan());
        var result = InformationTemplateDebtWriter.Run(repository.Path, gateway,
            ["initialize", "--protected-base", head, "--seed-lean-report", report]);
        if (active)
        {
            Assert.False(result.Success);
            Assert.Contains("DTR-Seed: initialization requires the original protected inactive seed", result.Error);
        }
        else
        {
            Assert.True(result.Success, "[FAIL] seed_initialization_accepts_clean_installed_head: " + result.Error);
        }
        Assert.Equal(activation.ToArray(), File.ReadAllBytes(activationPath));
        Assert.Empty(Git("status", "--porcelain"));
        var discharge = InformationTemplateDebtWriter.Run(repository.Path, gateway,
            ["discharge", "--protected-base", head]);
        Assert.False(discharge.Success);
        Assert.Contains("history comparison would be vacuous", discharge.Error);
        Git("checkout", "--detach", seed);
        var nonancestor = InformationTemplateDebtWriter.Run(repository.Path, gateway,
            ["initialize", "--protected-base", head, "--seed-lean-report", report]);
        Assert.False(nonancestor.Success);
        Assert.Contains("protected base must be an ancestor of HEAD", nonancestor.Error);
    }

    private static InformationTemplateUniverse Universe(InformationTemplateBindingState state)
    {
        var debt = Read();
        var occurrence = new InformationTemplateOccurrence(debt.Key, "Registration.lean", debt.StatementIdentity,
            debt.ContentInputs, state, state == InformationTemplateBindingState.DeclaredValidated ? new string('a', 64) : null,
            state == InformationTemplateBindingState.DeclaredUnresolved ? "IE-C050 reason=unclassified_form" : null,
            state == InformationTemplateBindingState.Undeclared ? null : "Binding.lean");
        return new(ImmutableDictionary<InformationOccurrenceKey, InformationTemplateOccurrence>.Empty.Add(debt.Key, occurrence),
            ImmutableHashSet.Create(debt.Key), ImmutableHashSet.Create("Registration.lean"), ImmutableHashSet.Create("Registration.lean"));
    }

    [Fact]
    public void immutable_base_seed_accepted()
    {
        var rows = InformationTemplateDebtWriter.Initialize(new(Seed, false), Seed,
            Snapshot(("Registration.lean", Source)), Universe(InformationTemplateBindingState.Undeclared));
        Assert.Equal(Row, System.Text.Encoding.UTF8.GetString(InformationTemplateDebtStore.WriteRow(Assert.Single(rows).Value).AsSpan()));
    }

    [Fact]
    public void seed_candidate_injection_rejected() =>
        Assert.Throws<FormatException>(() => InformationTemplateDebtWriter.Initialize(new(Seed, false),
            "a37c6134f47ae7f6faa9bf5d5cd0532b59c4d475", Snapshot(("Registration.lean", Source)),
            Universe(InformationTemplateBindingState.Undeclared)));

    [Fact]
    public void initialization_while_active_rejected() =>
        Assert.Throws<FormatException>(() => InformationTemplateDebtWriter.Initialize(new(Seed, true),
            Seed, Snapshot(("Registration.lean", Source)), Universe(InformationTemplateBindingState.Undeclared)));

    [Fact]
    public void seed_missing_base_input_rejected() =>
        Assert.Throws<FormatException>(() => InformationTemplateDebtWriter.Initialize(new(Seed, false),
            Seed, Snapshot(), Universe(InformationTemplateBindingState.Undeclared)));

    [Fact]
    public void writer_removes_exact_validated_row()
    {
        var row = Read();
        var debt = ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow>.Empty.Add(row.Key, row);
        Assert.Empty(InformationTemplateDebtWriter.Discharge(new(Seed, true), debt,
            Universe(InformationTemplateBindingState.DeclaredValidated)));
    }

    [Fact]
    public void writer_keeps_unresolved_row()
    {
        var row = Read();
        var debt = ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow>.Empty.Add(row.Key, row);
        Assert.Throws<FormatException>(() => InformationTemplateDebtWriter.Discharge(new(Seed, true), debt,
            Universe(InformationTemplateBindingState.DeclaredUnresolved)));
        Assert.Equal(row, Assert.Single(debt).Value);
    }

    [Fact]
    public void writer_keeps_undeclared_row()
    {
        var row = Read();
        var debt = ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow>.Empty.Add(row.Key, row);
        Assert.Equal(row, Assert.Single(InformationTemplateDebtWriter.Discharge(new(Seed, true), debt,
            Universe(InformationTemplateBindingState.Undeclared))).Value);
    }

    [Fact]
    public void writer_cannot_discharge_before_activation()
    {
        var row = Read();
        var debt = ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow>.Empty.Add(row.Key, row);
        Assert.Throws<FormatException>(() => InformationTemplateDebtWriter.Discharge(new(Seed, false), debt,
            Universe(InformationTemplateBindingState.DeclaredValidated)));
    }

    [Theory]
    [InlineData("Golden")]
    [InlineData("Golden/InformationTemplateDebt")]
    public void writer_rejects_directory_alias_before_publication(string alias)
    {
        var temporary = Directory.CreateTempSubdirectory("dtr-writer-");
        try
        {
            var root = Path.Combine(temporary.FullName, "repo");
            Directory.CreateDirectory(Path.Combine(root, ".git"));
            var outside = Directory.CreateDirectory(Path.Combine(temporary.FullName, "outside"));
            var link = Path.Combine(root, alias);
            Directory.CreateDirectory(Path.GetDirectoryName(link)!);
            Directory.CreateSymbolicLink(link, outside.FullName);
            var outputs = new Dictionary<string, ImmutableArray<byte>>
            {
                [InformationTemplateDebtStore.ActivationPath] = InformationTemplateDebtStore.WriteActivation(new(Seed, false)),
            };
            Assert.Throws<IOException>(() => InformationTemplateDebtWriter.Apply(root,
                new Dictionary<string, ImmutableArray<byte>>(), outputs, () => { }));
            Assert.Empty(Directory.GetFileSystemEntries(outside.FullName));
        }
        finally { temporary.Delete(true); }
    }

    [Fact]
    public void writer_restores_all_rows_after_partial_publication()
    {
        var temporary = Directory.CreateTempSubdirectory("dtr-writer-");
        try
        {
            var root = temporary.FullName;
            Directory.CreateDirectory(Path.Combine(root, ".git"));
            var first = InformationTemplateDebtStore.RowsRoot + new string('a', 64) + ".json";
            var second = InformationTemplateDebtStore.RowsRoot + new string('b', 64) + ".json";
            var original = ImmutableArray.Create<byte>(1, 2, 3);
            var before = new Dictionary<string, ImmutableArray<byte>> { [first] = original };
            Directory.CreateDirectory(Path.GetDirectoryName(Path.Combine(root, first))!);
            File.WriteAllBytes(Path.Combine(root, first), original.AsSpan());
            var after = new Dictionary<string, ImmutableArray<byte>>
            {
                [first] = ImmutableArray.Create<byte>(4), [second] = ImmutableArray.Create<byte>(5),
            };
            var publications = 0;
            Assert.Throws<IOException>(() => InformationTemplateDebtWriter.Apply(root, before, after, () => { },
                (source, target) =>
                {
                    if (++publications == 2) throw new IOException("injected second publication failure");
                    File.Move(source, target, true);
                }));
            Assert.Equal(original.ToArray(), File.ReadAllBytes(Path.Combine(root, first)));
            Assert.False(File.Exists(Path.Combine(root, second)));
        }
        finally { temporary.Delete(true); }
    }
}
