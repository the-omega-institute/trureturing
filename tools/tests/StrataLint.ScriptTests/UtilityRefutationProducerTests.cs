using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using FixtureFile = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

public sealed class UtilityRefutationProducerTests
{
    [Theory]
    [InlineData("expanded", "ChangedContent")]
    [InlineData("expanded", "PreDeposit")]
    [InlineData("expanded", "FirstFreeze")]
    [InlineData("companion", "ChangedContent")]
    [InlineData("companion", "PreDeposit")]
    [InlineData("companion", "FirstFreeze")]
    public void RealLeanAcceptsIrreducibleClaimRefutationsInEveryPhase(string result, string phase)
    {
        using var temporary = new TemporaryDirectory();
        var root = temporary.Path;
        const string path = "D5/S0/Carrier/RefutationProbe.lean";
        const string gid = "D5/S0/Carrier/RefutationProbe";
        const string module = "D5.S0.Carrier.RefutationProbe";
        const string claimGid = gid + ".claim";
        var utility = $"kind=certified-instance; basis=refutes=gid:{claimGid}; result={gid}.{result}; claim={claimGid}";
        var source = $"/- GID: {gid}\n   generality: I\n   mirror-B: D5/B/S0/Carrier/RefutationProbe\n"
            + "   mirror-E: none(waiver:pure-definition)\n   anchors: []\n"
            + $"   utility: {utility}\n   digest: Synthetic irreducible claim refutation. -/\n"
            + """
            @[irreducible] def claim : Prop := forall n : Nat, n + 1 = n
            theorem expanded : Not (forall n : Nat, n + 1 = n) := by
              intro h
              exact Nat.noConfusion (h 0)
            theorem companion : Not claim := by
              unfold claim
              exact expanded
            """ + "\n";
        var sourceHash = "sha256:" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(source)));
        Directory.CreateDirectory(Path.Combine(root, "D5", "S0", "Carrier"));
        File.Copy(Path.Combine(TestRepositoryLayout.FindRoot(), "lean-toolchain"), Path.Combine(root, "lean-toolchain"));
        File.WriteAllText(Path.Combine(root, "lakefile.toml"),
            "name = \"refutation_fixture\"\ndefaultTargets = [\"D5\"]\n[[lean_lib]]\nname = \"D5\"\nglobs = [\"D5.+\"]\n");
        File.WriteAllText(Path.Combine(root, path), source);
        RequireSuccess(TestProcessRunner.Run("lake", ["build"], root,
            TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024));

        var inspector = Path.Combine(TestRepositoryLayout.FindRoot(), "tools", "lean-inspector", "Inspector.lean");
        var compactor = Path.Combine(TestRepositoryLayout.FindRoot(), "tools", "lean-inspector", "materials.py");
        var inputs = Path.Combine(root, "utility.json");
        var output = Path.Combine(root, "report.json");
        File.WriteAllText(inputs, JsonSerializer.Serialize(new[] { new {
            modulePath = path, claimGid, claimModule = module, claimSelector = "claim",
            claimSourcePath = path, claimSourceSha256 = sourceHash,
            resultGid = gid + "." + result, resultModule = module, resultSelector = result,
        } }));
        RequireSuccess(TestProcessRunner.Run("lake", ["env", "lean", "--run", inspector,
            "--output", output + ".spool", "--material-spool", output + ".materials",
            "--utility-input", inputs, module, path, sourceHash], root,
            TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024));
        RequireSuccess(TestProcessRunner.Run("python3", [compactor, "compact", output + ".spool", output + ".materials", output], root,
            TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create([RawRepositoryEntry.FromText(path, source)]))).Snapshot;
        var report = RawLeanReportArtifact.ReadFile(output, snapshot);
        var validation = UtilityDeclarationValidator.Validate(Enum.Parse<UtilityValidationPhase>(phase),
            RepoPath.CreateKnown(path), utility, snapshot, () => report);

        Assert.True(validation.IsAccepted, $"{result}/{phase}: {validation.Failure} {validation.Detail}");
        Assert.True(report.Files[RepoPath.CreateKnown(path)].Refutation!.IsClosedNegation);
    }

    [Fact]
    public void RealLeanProducesTypedRefutationsAndRejectsPositiveOrConditionalRelabeling()
    {
        using var temporary = new TemporaryDirectory();
        var root = temporary.Path;
        var moduleDirectory = Path.Combine(root, "D5", "S0", "Carrier");
        Directory.CreateDirectory(moduleDirectory);
        const string path = "D5/S0/Carrier/Probe.lean";
        const string gid = "D5/S0/Carrier/Probe";
        const string externalPath = "D5/S0/Carrier/Law.lean";
        const string externalSource = "def external_law : Prop := forall n : Nat, n + 1 = n\n";
        const string declarations = """
            def proposed_law : Prop := forall n : Nat, n + 1 = n
            theorem direct : Not proposed_law := by
              intro h
              exact Nat.noConfusion (h 0)
            theorem witness : Exists (fun n : Nat => Not (n + 1 = n)) := by
              exact Exists.intro 0 (by decide)
            theorem bridged : Not proposed_law := by
              intro h
              obtain ⟨n, hn⟩ := witness
              exact hn (h n)
            theorem conjunction : Not (0 + 1 = 0) ∧ True := by decide
            theorem conjunction_bridge : Not proposed_law := by
              intro h
              exact conjunction.1 (h 0)
            theorem positive : 17 + 4 = 21 := rfl
            theorem conditional (h : False) : Not proposed_law := False.elim h
            def not_a_theorem : Not proposed_law := direct
            def other_claim : Prop := True
            def parameterized_claim (n : Nat) : Prop := n + 1 = n
            theorem general (n : Nat) : n + 0 = n := rfl
            """ + "\n";
        File.Copy(Path.Combine(TestRepositoryLayout.FindRoot(), "lean-toolchain"), Path.Combine(root, "lean-toolchain"));
        File.WriteAllText(Path.Combine(root, "lakefile.toml"),
            "name = \"refutation_fixture\"\ndefaultTargets = [\"D5\"]\n[[lean_lib]]\nname = \"D5\"\nglobs = [\"D5.+\"]\n");
        File.WriteAllText(Path.Combine(root, path), declarations);
        File.WriteAllText(Path.Combine(root, externalPath), externalSource);
        RequireSuccess(TestProcessRunner.Run("lake", ["build"], root,
            TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024));

        var inspector = Path.Combine(TestRepositoryLayout.FindRoot(), "tools", "lean-inspector", "Inspector.lean");
        var compactor = Path.Combine(TestRepositoryLayout.FindRoot(), "tools", "lean-inspector", "materials.py");
        var inputs = Path.Combine(root, "utility.json");
        var output = Path.Combine(root, "report.json");
        foreach (var (result, claim, valid) in new[] {
            ("direct", "proposed_law", true), ("bridged", "proposed_law", true),
            ("conjunction_bridge", "proposed_law", true), ("positive", "proposed_law", false),
            ("witness", "proposed_law", false), ("conditional", "proposed_law", false),
            ("not_a_theorem", "proposed_law", false), ("direct", "other_claim", false),
            ("direct", "parameterized_claim", false), ("general", "proposed_law", false),
            ("direct", "external_law", true),
        })
        {
            var claimModule = claim == "external_law" ? "D5.S0.Carrier.Law" : "D5.S0.Carrier.Probe";
            var claimGid = (claim == "external_law" ? "D5/S0/Carrier/Law" : gid) + "." + claim;
            var utility = $"kind=certified-instance; basis=refutes=gid:{claimGid}; result={gid}.{result}; claim={claimGid}";
            var source = $"/- GID: {gid}\n   generality: I\n   mirror-B: D5/B/S0/Carrier/Probe\n"
                + "   mirror-E: none(waiver:pure-definition)\n   anchors: []\n"
                + $"   utility: {utility}\n   digest: Synthetic refutation. -/\n" + declarations;
            File.WriteAllText(Path.Combine(root, path), source);
            RequireSuccess(TestProcessRunner.Run("lake", ["build"], root,
                TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024));
            File.WriteAllText(inputs, JsonSerializer.Serialize(new[] { new {
                modulePath = path, claimGid, claimModule, claimSelector = claim,
                claimSourcePath = claim == "external_law" ? externalPath : path,
                claimSourceSha256 = "sha256:" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(
                    claim == "external_law" ? externalSource : source))),
                resultGid = gid + "." + result, resultModule = "D5.S0.Carrier.Probe", resultSelector = result,
            } }));
            RequireSuccess(TestProcessRunner.Run("lake", ["env", "lean", "--run", inspector,
                "--output", output + ".spool", "--material-spool", output + ".materials",
                "--utility-input", inputs, "D5.S0.Carrier.Probe", path,
                "sha256:" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(source))),
                "D5.S0.Carrier.Law", externalPath,
                "sha256:" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(externalSource)))], root,
                TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024));
            RequireSuccess(TestProcessRunner.Run("python3", [compactor, "compact", output + ".spool", output + ".materials", output], root,
                TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024));
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
                RawRepositorySnapshot.Create([RawRepositoryEntry.FromText(path, source),
                    RawRepositoryEntry.FromText(externalPath, externalSource)]))).Snapshot;
            var report = RawLeanReportArtifact.ReadFile(output, snapshot);
            Assert.Equal(valid, report.Files[RepoPath.CreateKnown(path)].Refutation!.IsClosedNegation);
            foreach (var phase in Enum.GetValues<UtilityValidationPhase>())
            {
                var validation = UtilityDeclarationValidator.Validate(phase, RepoPath.CreateKnown(path), utility, snapshot, () => report);
                Assert.Equal(valid, validation.IsAccepted);
            }

            if (claim == "external_law")
            {
                // A delta report may inspect only the changed result, with its claim reused from the baseline.
                RequireSuccess(TestProcessRunner.Run("lake", ["env", "lean", "--run", inspector,
                    "--output", output + ".subset.spool", "--material-spool", output + ".subset.materials",
                    "--utility-input", inputs, "D5.S0.Carrier.Probe", path,
                    "sha256:" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(source)))], root,
                    TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024));
                RequireSuccess(TestProcessRunner.Run("python3", [compactor, "compact", output + ".subset.spool", output + ".subset.materials",
                    output + ".subset"], root,
                    TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024));
                using var subset = JsonDocument.Parse(FixtureFile.ReadAllBytes(output + ".subset"));
                var modules = subset.RootElement.GetProperty("modules");
                Assert.Equal(1, modules.GetArrayLength());
                Assert.True(modules[0].GetProperty("utility_refutation").GetProperty("is_closed_negation").GetBoolean());
            }
        }
    }

    private static void RequireSuccess(ProcessOutput result)
    {
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
