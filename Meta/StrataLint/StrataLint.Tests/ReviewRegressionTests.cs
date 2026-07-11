using System.Diagnostics;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ReviewRegressionTests
{
    [Fact]
    public void Cf1TopologyReportsBootstrapNotActiveWhenDefaultBranchLacksWorkflow()
    {
        using var remote = new TemporaryDirectory();
        using var repository = new TemporaryDirectory();
        InitializeRemoteDefaultBranch(remote.Path, repository.Path, installWorkflow: false);
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            new[] { "topology" },
            new ProductionCliEnvironment(repository.Path),
            console);

        Assert.Equal(3, exitCode);
        Assert.Contains(
            "BOOTSTRAP-NOT-ACTIVE:baseline gate 尚未注入 dev,当前非机器门控态,须人类可信注入(D5-T0017)",
            console.Output,
            StringComparison.Ordinal);
        Assert.DoesNotContain("STEADY-STATE-ACTIVE", console.Output, StringComparison.Ordinal);
        Assert.Equal(string.Empty, console.Error);
    }

    [Fact]
    public void Cf1TopologyReportsSteadyStateWhenDefaultBranchContainsWorkflow()
    {
        using var remote = new TemporaryDirectory();
        using var repository = new TemporaryDirectory();
        InitializeRemoteDefaultBranch(remote.Path, repository.Path, installWorkflow: true);
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            new[] { "topology" },
            new ProductionCliEnvironment(repository.Path),
            console);

        Assert.Equal(0, exitCode);
        Assert.Contains(
            "STEADY-STATE-ACTIVE:dev-baseline workflow 已注入 dev;required_status_checks/enforce_admins 仍须外部核验(D5-T0017)",
            console.Output,
            StringComparison.Ordinal);
        Assert.DoesNotContain("BOOTSTRAP-NOT-ACTIVE", console.Output, StringComparison.Ordinal);
        Assert.Equal(string.Empty, console.Error);
    }

    [Fact]
    public void Cf1BootstrapTicketCannotDisappearFromProtectedBackfillInventory()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files["Meta/BACKFILL.yaml"] = fixture.Files["Meta/BACKFILL.yaml"].Replace(
            "  - case_id: D5-T0017\n    gid: D5/X_Frontier/RequiredChecks\n",
            string.Empty,
            StringComparison.Ordinal);

        var evaluation = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(16), fixture.Build());

        Assert.Contains(
            evaluation.Diagnostics,
            diagnostic => diagnostic.Message.Contains("D5-T0017", StringComparison.Ordinal));
    }

    [Fact]
    public void Cf2RenameReportsBothProtectedOldPathAndNewPath()
    {
        using var repository = new TemporaryDirectory();
        RunGit(repository.Path, "init");
        RunGit(repository.Path, "config", "user.email", "stratalint@example.invalid");
        RunGit(repository.Path, "config", "user.name", "StrataLint Tests");
        var oldPath = Path.Combine(repository.Path, "Meta", "StrataLint", "Gate.txt");
        Directory.CreateDirectory(
            Path.GetDirectoryName(oldPath)
                ?? throw new InvalidOperationException("protected fixture path has no parent"));
        File.WriteAllText(oldPath, "protected\n", new UTF8Encoding(false));
        RunGit(repository.Path, "add", ".");
        RunGit(repository.Path, "commit", "-m", "baseline");
        var baseline = RunGit(repository.Path, "rev-parse", "HEAD").Trim();
        Directory.CreateDirectory(Path.Combine(repository.Path, "notes"));
        RunGit(repository.Path, "mv", "Meta/StrataLint/Gate.txt", "notes/Gate.txt");

        var prepared = new GitRepositoryGateway(repository.Path).Prepare(baseline);

        Assert.Contains(prepared.Changes.Paths, path => path.Value == "Meta/StrataLint/Gate.txt");
        Assert.Contains(prepared.Changes.Paths, path => path.Value == "notes/Gate.txt");
        var review = Assert.IsType<BootstrapOutcome.HumanReviewRequired>(
            BootstrapGate.Evaluate(prepared.Changes));
        Assert.Contains(review.ChangeSet.Paths, path => path.Value == "Meta/StrataLint/Gate.txt");
    }

    [Theory]
    [InlineData("Evidence/D5/S0/Carrier/Probe.result.toml")]
    [InlineData("Evidence/D5/S0/Carrier/Probe.spec.json")]
    public void Cf3ReversePathValidationRejectsRegistryUnknownKindOrSelector(string path)
    {
        var fixture = new RuleFixture();
        fixture.Files[path] = "{}\n";
        var context = fixture.BuildForRuleCompatibility();

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.Execute(context));
        var diagnostic = Assert.Single(completed.Capability.Diagnostics, item => item.Path == path);
        Assert.Equal(RuleId.CreateKnown(15), diagnostic.RuleId);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);

        var policy = AcceptedPolicy(TestRegistry.Canonical);
        var canonical = RepositoryCanonicalizer.Validate(context.Current, policy);
        Assert.IsType<CanonicalizationOutcome.InfrastructureFailure>(canonical);
    }

    [Fact]
    public void Cf4Sl019ScansResidualScalarAfterAValidEmbeddedObject()
    {
        var fixture = new RuleFixture();
        const string path = "Evidence/D5/S0/Carrier/Mixed.run.json";
        fixture.Files[path] = "{\"payload\": \"prefix {\\\"note\\\":\\\"ok\\\"} anomaly tail\"}\n";

        var evaluation = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(19), fixture.Build());

        var diagnostic = Assert.Single(evaluation.Diagnostics, item => item.Path == path);
        Assert.Contains("unknown anomaly-bearing schema at $.payload", diagnostic.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(
        "Evidence/D5/S0/Carrier/Canonical.run.json",
        "{\"alpha\": 1, \"omega\": 2}\n",
        "{\"alpha\":1,\"omega\":2}\n")]
    [InlineData(
        "Evidence/D5/S0/Carrier/Canonical.run.yaml",
        "alpha: 1\nomega: 2\n",
        "alpha:  1\nomega: 2\n")]
    public void Cf5CanonicalizationComparesRawStructuredBytes(
        string path,
        string canonicalBytes,
        string noncanonicalBytes)
    {
        var fixture = new RuleFixture();
        var policy = AcceptedPolicy(TestRegistry.Canonical);
        fixture.Files[path] = canonicalBytes;
        var canonicalSnapshot = fixture.BuildForRuleCompatibility().Current;
        Assert.IsType<CanonicalizationOutcome.Accepted>(
            RepositoryCanonicalizer.Validate(canonicalSnapshot, policy));

        fixture.Files[path] = noncanonicalBytes;
        var noncanonicalSnapshot = fixture.BuildForRuleCompatibility().Current;
        var rejected = RepositoryCanonicalizer.Validate(noncanonicalSnapshot, policy);

        var failure = Assert.IsType<CanonicalizationOutcome.InfrastructureFailure>(rejected);
        Assert.Contains("canonical", failure.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void Cf6ProductionRouteRejectsDomainMissingFromDomainsYaml()
    {
        using var repository = new TemporaryDirectory();
        Directory.CreateDirectory(Path.Combine(repository.Path, "Meta"));
        File.WriteAllText(
            Path.Combine(repository.Path, "Meta", "registry.yaml"),
            TestRegistry.Canonical,
            new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(repository.Path, "Meta", "domains.yaml"),
            "domains:\n  Conventions:\n    stratum: S0\n    definition: Fixture.\n",
            new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(repository.Path, "manifest.json"),
            "{\"artifact\":\"lean\",\"domain\":\"Carrier\",\"generality\":\"G\",\"module\":\"Probe\",\"plane\":\"F\",\"selector\":\"\",\"tag\":\"\",\"theory\":\"D5\"}\n",
            new UTF8Encoding(false));
        var environment = new ProductionCliEnvironment(
            repository.Path,
            new FakeRepositoryGateway(RawChangeSet.Create(Array.Empty<string>()), null, null),
            new FakeLeanInspector(null));

        var result = environment.Route(new[] { "manifest.json" });

        Assert.False(result.Success);
        Assert.Contains("controlled domain", result.Error, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void Cf7UnknownLeanAxiomIsSl020BlockInsteadOfInfrastructureFailure()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var baselineReport = LeanAxiomReport.Create(fixture.BaselineReports);
        fixture.SetRingDeclaration("invented", "theorem", "unregistered.axiom");
        var currentReport = LeanAxiomReport.Create(fixture.Reports);
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create(new[] { RuleFixture.BlueprintPath }),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline));
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new SequencedLeanInspector(currentReport, baselineReport));

        var outcome = environment.Check(Array.Empty<string>());

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var diagnostic = Assert.Single(
            rejected.Diagnostics,
            item => item.RuleId == RuleId.CreateKnown(20)
                && item.Message.Contains("unregistered.axiom", StringComparison.Ordinal));
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
    }

    [Fact]
    public void Cf8ClosedWorldShapeFailuresKeepPythonSl000DiagnosticCode()
    {
        Assert.True(RuleId.TryCreate("SL-000", out var sl000));
        var fixture = new RuleFixture();
        fixture.Files["rogue.txt"] = "unknown\n";

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.BuildForRuleCompatibility()));

        var diagnostic = Assert.Single(completed.Capability.Diagnostics, item => item.Path == "rogue.txt");
        Assert.Equal(sl000, diagnostic.RuleId);
        Assert.Equal("unknown top-level artifact", diagnostic.Message);
    }

    [Fact]
    public void Cf9BackfillProtectedPathMembershipComesFromRegistry()
    {
        const string sourcePath = "docs/develop/spec/golden-ledger-repo-spec.md";
        var registryWithoutSource = TestRegistry.Canonical.Replace(
            $"  - \"{sourcePath}\"\n",
            string.Empty,
            StringComparison.Ordinal);
        var policy = AcceptedPolicy(registryWithoutSource);
        var fixture = new RuleFixture();

        var evaluation = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(16), fixture.Build(policy));

        Assert.Contains(
            evaluation.Diagnostics,
            item => item.Message.Contains("protected source spec-v7.11-section-10 path changed", StringComparison.Ordinal));
        var engineSource = File.ReadAllText(
            Path.Combine(FindRepositoryRoot(), "Meta", "StrataLint", "StrataLint.Engine", "BackfillInventoryRule.cs"),
            Encoding.UTF8);
        Assert.DoesNotContain(sourcePath, engineSource, StringComparison.Ordinal);
        Assert.DoesNotContain("GICT_complete_development_v3 (3).md", engineSource, StringComparison.Ordinal);
        Assert.DoesNotContain("PZG_BEDC_kernel_formal_170.md", engineSource, StringComparison.Ordinal);
    }

    [Fact]
    public void Cf10AdmissionWorkflowRunsRepositoryCheckAndByteStableSelftest()
    {
        var workflow = File.ReadAllText(
            Path.Combine(FindRepositoryRoot(), ".github", "workflows", "ci.yml"),
            Encoding.UTF8);

        Assert.Contains("check --protected-base", workflow, StringComparison.Ordinal);
        Assert.True(Count(workflow, " selftest") >= 2, "selftest must run twice");
        Assert.Contains("cmp", workflow, StringComparison.Ordinal);
    }

    private static ValidatedPolicy AcceptedPolicy(string registry)
    {
        var outcome = RegistryLoader.Load(
            Encoding.UTF8.GetBytes(registry),
            Encoding.UTF8.GetBytes(TestRegistry.Domains));
        return Assert.IsType<RegistryLoadOutcome.Accepted>(outcome).Policy;
    }

    private static RawRepositorySnapshot Snapshot(IReadOnlyDictionary<string, string> files) =>
        RawRepositorySnapshot.Create(files.Select(pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));

    private static int Count(string value, string fragment) =>
        (value.Length - value.Replace(fragment, string.Empty, StringComparison.Ordinal).Length) / fragment.Length;

    private static void InitializeRemoteDefaultBranch(
        string remoteRoot,
        string repositoryRoot,
        bool installWorkflow)
    {
        RunGit(remoteRoot, "init", "--bare", "--initial-branch=dev");
        RunGit(repositoryRoot, "init", "--initial-branch=dev");
        RunGit(repositoryRoot, "config", "user.email", "stratalint@example.invalid");
        RunGit(repositoryRoot, "config", "user.name", "StrataLint Tests");
        File.WriteAllText(
            Path.Combine(repositoryRoot, "README.md"),
            "# topology fixture\n",
            new UTF8Encoding(false));
        if (installWorkflow)
        {
            var workflowDirectory = Path.Combine(repositoryRoot, ".github", "workflows");
            Directory.CreateDirectory(workflowDirectory);
            File.Copy(
                Path.Combine(FindRepositoryRoot(), ".github", "workflows", "ci.yml"),
                Path.Combine(workflowDirectory, "ci.yml"));
        }

        RunGit(repositoryRoot, "add", ".");
        RunGit(repositoryRoot, "commit", "-m", "default branch fixture");
        RunGit(repositoryRoot, "remote", "add", "origin", remoteRoot);
        RunGit(repositoryRoot, "push", "--set-upstream", "origin", "dev");
    }

    private static string RunGit(string root, params string[] arguments)
    {
        var startInfo = new ProcessStartInfo("git")
        {
            WorkingDirectory = root,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        foreach (var argument in arguments)
        {
            startInfo.ArgumentList.Add(argument);
        }

        using var process = Process.Start(startInfo) ?? throw new InvalidOperationException("git did not start");
        var stdout = process.StandardOutput.ReadToEnd();
        var stderr = process.StandardError.ReadToEnd();
        process.WaitForExit();
        Assert.True(process.ExitCode == 0, $"git {string.Join(' ', arguments)} failed: {stderr}");
        return stdout;
    }

    private static string FindRepositoryRoot()
    {
        var directory = new DirectoryInfo(AppContext.BaseDirectory);
        while (directory is not null)
        {
            if (File.Exists(Path.Combine(directory.FullName, ".github", "workflows", "ci.yml")))
            {
                return directory.FullName;
            }

            directory = directory.Parent;
        }

        throw new DirectoryNotFoundException("could not locate repository root");
    }

    private sealed class SequencedLeanInspector(params LeanAxiomReport[] reports) : ILeanInspector
    {
        private int index;

        public LeanAxiomReport Inspect(RepositorySnapshot snapshot) =>
            index < reports.Length
                ? reports[index++]
                : throw new InvalidOperationException("Lean inspector was called too many times");
    }
}
