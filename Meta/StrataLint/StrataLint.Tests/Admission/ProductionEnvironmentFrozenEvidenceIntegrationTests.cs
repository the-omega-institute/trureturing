using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{

    private static RealFrozenEvidenceInvocation CreateRealFrozenEvidenceInvocation(
        string candidateRoot,
        string evidenceRoot,
        string reportRoot,
        bool useMissingCommit)
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files["lean-toolchain"] = "leanprover/lean4:v4.24.0\n";
        fixture.Files["lake-manifest.json"] = "{}\n";
        Replace(fixture.Baseline, fixture.Files);
        Replace(fixture.BaselineReports, fixture.Reports);

        InitializeRepository(evidenceRoot);
        WriteFiles(evidenceRoot, fixture.Baseline);
        ReviewRegressionTests.RunGit(evidenceRoot, "add", ".");
        ReviewRegressionTests.RunGit(evidenceRoot, "commit", "-m", "non-ancestor frozen evidence");
        var evidenceCommit = GitText(evidenceRoot, "rev-parse", "HEAD");
        var evidenceTree = GitText(evidenceRoot, "rev-parse", "HEAD^{tree}");
        var prefix = evidenceCommit.Length == 40 ? "git-sha1:" : "git-sha256:";
        var environment = new FrozenEnvironmentAttestation(
            useMissingCommit ? "git-sha1:" + new string('f', 40) : prefix + evidenceCommit,
            prefix + evidenceTree,
            prefix + GitText(evidenceRoot, "rev-parse", "HEAD:lean-toolchain"),
            prefix + GitText(evidenceRoot, "rev-parse", "HEAD:lake-manifest.json"));
        var state = BuildState(fixture.Baseline, fixture.BaselineReports);
        var attestations = state.Dag.Nodes
            .Where(static node => node.State is TruthState.Closed && node.ModuleName is not null)
            .Select(node => new FrozenModuleAttestation(
                node.RepoPath,
                prefix + GitText(evidenceRoot, "rev-parse", $"HEAD:{node.RepoPath.Value}")))
            .ToImmutableArray();
        var catalog = Assert.IsType<FrozenMaterialOutcome.Accepted>(FrozenContentAddress.Build(
            state.Snapshot,
            state.Lean,
            state.Dag,
            environment,
            attestations)).Capability;
        var generatorBlob = prefix + GitText(evidenceRoot, "rev-parse", "HEAD:Meta/registry.yaml");
        var ledger = Encoding.UTF8.GetString(FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(generatorBlob, RuleCatalog.Default.RootSha256)).AsSpan());
        SetLedger(fixture.Baseline, ledger);
        SetLedger(fixture.Files, ledger);

        InitializeRepository(candidateRoot);
        WriteFiles(candidateRoot, fixture.Baseline);
        ReviewRegressionTests.RunGit(candidateRoot, "add", ".");
        ReviewRegressionTests.RunGit(candidateRoot, "commit", "-m", "protected baseline");
        var baselineCommit = GitText(candidateRoot, "rev-parse", "HEAD");
        fixture.Files["Library/queries.yaml"] += "\n";
        WriteFiles(candidateRoot, fixture.Files);
        ReviewRegressionTests.RunGit(candidateRoot, "add", ".");
        ReviewRegressionTests.RunGit(candidateRoot, "commit", "-m", "candidate ordinary change");

        var candidateReport = Path.Combine(reportRoot, "candidate.json");
        var baselineReport = Path.Combine(reportRoot, "baseline.json");
        File.WriteAllBytes(
            candidateReport,
            RawLeanReportArtifact.Write(
                Decode(Snapshot(fixture.Files)),
                LeanAxiomReport.Create(fixture.Reports)).AsSpan());
        File.WriteAllBytes(
            baselineReport,
            RawLeanReportArtifact.Write(
                Decode(Snapshot(fixture.Baseline)),
                LeanAxiomReport.Create(fixture.BaselineReports)).AsSpan());
        return new RealFrozenEvidenceInvocation(
            baselineCommit,
            evidenceCommit,
            [
                "--protected-base", baselineCommit,
                "--candidate-lean-report", candidateReport,
                "--baseline-lean-report", baselineReport,
                "--frozen-evidence-root", evidenceRoot,
            ]);
    }

    private static void InitializeRepository(string root)
    {
        ReviewRegressionTests.RunGit(root, "init", "-b", "dev");
        ReviewRegressionTests.RunGit(root, "config", "user.email", "stratalint@example.invalid");
        ReviewRegressionTests.RunGit(root, "config", "user.name", "StrataLint Tests");
    }

    private static void WriteFiles(string root, IReadOnlyDictionary<string, string> files)
    {
        foreach (var (path, text) in files)
        {
            var absolute = Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar));
            Directory.CreateDirectory(Path.GetDirectoryName(absolute)!);
            File.WriteAllText(absolute, text, new UTF8Encoding(false));
        }
    }

    private static void Replace<T>(IDictionary<string, T> destination, IReadOnlyDictionary<string, T> source)
    {
        destination.Clear();
        foreach (var (key, value) in source) destination.Add(key, value);
    }

    private static string GitText(string root, params string[] arguments) =>
        ReviewRegressionTests.RunGit(root, arguments).Trim();

    private sealed record RealFrozenEvidenceInvocation(
        string BaselineCommit,
        string EvidenceCommit,
        string[] Arguments);
}
