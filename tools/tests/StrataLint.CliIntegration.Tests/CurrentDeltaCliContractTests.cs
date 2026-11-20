using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Cli;

namespace StrataLint.CliIntegration.Tests;

public sealed class CurrentDeltaCliContractTests
{
    [Theory]
    [InlineData("check-current", false)]
    [InlineData("check-delta", true)]
    public void StandaloneChecksRequireAnExplicitInputAndRejectMixedOrRetiredArguments(string command, bool delta)
    {
        using var fixture = new TemporaryDirectory();
        List<string[]> scenarios = [ [], ["--common-current", "current.json"],
            ["--common-engineering", "engineering.json"], ["--build-round", "round.json"],
            ["--scoped-reports-from", "reports"],
            ["--candidate-lean-report", "report", "--changed-paths-from", "paths"],
            ["--changed-paths-from", "paths", "--scribe-paths-from", "other-paths"] ];
        if (delta) scenarios.Add(["--candidate-lean-report", "report.json"]);
        else scenarios.Add(["--protected-base", new string('a', 40), "--candidate-lean-report", "report.json"]);
        foreach (var arguments in scenarios)
        {
            var result = TestProcessRunner.Run("dotnet", [typeof(StrataLint.Cli.Program).Assembly.Location, command, .. arguments],
                fixture.Path, TestBudgets.ScriptProcessHangGuard, 64 * 1024);
            Assert.Equal(2, result.ExitCode);
            Assert.Contains("INFRASTRUCTURE_FAILURE", Encoding.UTF8.GetString(result.StandardError));
            Assert.False(Directory.Exists(Path.Combine(fixture.Path, "build/ci")));
        }
    }

    [Fact]
    public void CliRuntimeConfigurationConservesGarbageCollectedMemory()
    {
        var path = Path.ChangeExtension(typeof(StrataLint.Cli.Program).Assembly.Location, ".runtimeconfig.json");
        using var document = System.Text.Json.JsonDocument.Parse(File.ReadAllBytes(path));
        var properties = document.RootElement.GetProperty("runtimeOptions").GetProperty("configProperties");
        Assert.Equal(9, properties.GetProperty("System.GC.ConserveMemory").GetInt32());
    }

    [Fact]
    public void CurrentReadsAParentlessRemotelessRepositoryBeforeReportingMissingReport()
    {
        using var fixture = new TemporaryDirectory();
        void Git(params string[] args) => Assert.Equal(0, TestProcessRunner.Run("git", args, fixture.Path,
            TestBudgets.ScriptProcessHangGuard, 64 * 1024).ExitCode);
        File.WriteAllText(Path.Combine(fixture.Path, "README.md"), "fixture\n");
        Git("init", "-q"); Git("add", ".");
        Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "parentless");
        var result = TestProcessRunner.Run("dotnet", [typeof(StrataLint.Cli.Program).Assembly.Location, "check-current",
            "--candidate-lean-report", Path.Combine(fixture.Path, "absent-report.json")], fixture.Path,
            TestBudgets.ScriptProcessHangGuard, 64 * 1024);
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("absent-report.json", Encoding.UTF8.GetString(result.StandardError));
        Assert.False(Directory.Exists(Path.Combine(fixture.Path, "build/ci")));
    }

    [Fact]
    public void ScopedDeltaChecksExactChangedPathsIncludingBothRenameEndpoints()
    {
        using var fixture = new TemporaryDirectory();
        var path = Path.Combine(fixture.Path, "changes");
        var changes = RawChangeSet.CreateWithKinds([
            ("D5/Old.lean", RawChangeKind.Deleted), ("D5/New.lean", RawChangeKind.Added),
            ("D5/CopySource.lean", RawChangeKind.Copied), ("D5/Copy.lean", RawChangeKind.Added)]);
        var prepared = new PreparedRepository(new string('a', 40), changes);
        File.WriteAllText(path, "D5/New.lean\0D5/Copy.lean\0");
        Assert.Throws<InvalidDataException>(() => ScopedAdmissionReports.ChangedPaths(path, prepared));
        File.AppendAllText(path, "D5/Old.lean\0");
        Assert.Equal(3, ScopedAdmissionReports.ChangedPaths(path, prepared).Paths.Length);
        File.AppendAllText(path, "README.md");
        Assert.Throws<InvalidDataException>(() => ScopedAdmissionReports.ChangedPaths(path, null));
    }

    [Fact]
    public void ScopedBatchesCheckMembershipProvenanceAndAgreementOfSharedDependencies()
    {
        using var fixture = new TemporaryDirectory();
        var scripts = Directory.CreateDirectory(Path.Combine(fixture.Path, "tools/scripts/report")).FullName;
        // Exercise the verifier boundary with an attestation success and failure in this fixture.
        File.WriteAllText(Path.Combine(scripts, "lean-report-input.sh"),
            "test \"$1\" = verify-scoped && test \"$(cat \"$5.input.attestation\")\" = verified\n");
        var shared = RawRepositoryEntry.FromText("D5/Shared.lean", "prelude\n");
        var a = RawRepositoryEntry.FromText("D5/A.lean", "prelude\nimport D5.Shared\n");
        var b = RawRepositoryEntry.FromText("D5/B.lean", "prelude\nimport D5.Shared\n");
        var snapshot = Decode(shared, a, b);
        var manifest = Path.Combine(fixture.Path, "reports");
        var first = Bundle(a, "D5.A", "shared-evidence");
        var second = Bundle(b, "D5.B", "shared-evidence");
        File.WriteAllText(manifest, first + "\0" + second + "\0");

        var union = ScopedAdmissionReports.Read(fixture.Path, snapshot, ["D5.A", "D5.B"], manifest);
        Assert.True(union.IsScoped);
        Assert.Equal(3, union.Files.Count);
        Assert.Empty(ScopedAdmissionReports.Read(fixture.Path, snapshot, [], null).Files);
        Assert.Throws<InvalidDataException>(() => ScopedAdmissionReports.Read(fixture.Path, snapshot, ["D5.A"], null));
        Assert.Throws<InvalidDataException>(() => ScopedAdmissionReports.Read(fixture.Path, snapshot, ["D5.A"], manifest));
        File.WriteAllText(second + ".input.attestation", "stale");
        Assert.Throws<InvalidOperationException>(() => ScopedAdmissionReports.Read(fixture.Path, snapshot, ["D5.A", "D5.B"], manifest));
        Bundle(b, "D5.B", "different-evidence");
        Assert.Contains("disagree", Assert.Throws<InvalidDataException>(() =>
            ScopedAdmissionReports.Read(fixture.Path, snapshot, ["D5.A", "D5.B"], manifest)).Message);

        string Bundle(RawRepositoryEntry owner, string module, string sharedDigest)
        {
            var path = Path.Combine(fixture.Path, module + ".json");
            var content = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport> {
                [owner.Path] = new(["D5.Shared"], []), [shared.Path] = new([], []) });
            RawLeanReportArtifact.WriteFile(path, Decode(owner, shared), content);
            File.WriteAllText(path, File.ReadAllText(path).Replace(RawLeanReportArtifact.Schema, RawLeanReportArtifact.ScopedSchema,
                StringComparison.Ordinal));
            var origins = new Dictionary<string, object> {
                [module] = new { report_sha256 = module }, ["D5.Shared"] = new { report_sha256 = sharedDigest } };
            File.WriteAllText(path + ".provenance.json", JsonSerializer.Serialize(new {
                inputs = new { scope = new { roots = new[] { module } } }, module_origins = origins }));
            File.WriteAllText(path + ".sha256", "fixture");
            File.WriteAllText(path + ".input.attestation", "verified");
            return path;
        }

        static RepositorySnapshot Decode(params RawRepositoryEntry[] entries) =>
            Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create(entries))).Snapshot;
    }
}
