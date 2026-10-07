using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using FixtureFile = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

public sealed class UtilityRefutationProducerTests
{
    [Theory]
    [InlineData("expanded", "ChangedContent", false)]
    [InlineData("expanded", "PreDeposit", false)]
    [InlineData("expanded", "FirstFreeze", false)]
    [InlineData("companion", "ChangedContent", true)]
    [InlineData("companion", "PreDeposit", true)]
    [InlineData("companion", "FirstFreeze", true)]
    public void RealLeanChecksLiteralIrreducibleClaimRefutationsInEveryPhase(string result, string phase, bool valid)
    {
        using var temporary = new TemporaryDirectory();
        var root = temporary.Path;
        var manifest = Path.Combine(root, LeanReportRegistrationFixture.ManifestPath);
        File.WriteAllText(manifest, LeanReportRegistrationFixture.Manifest);
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
            "name = \"refutation_fixture\"\ndefaultTargets = [\"D5\", \"LeanInformationAudit\"]\n[[lean_lib]]\nname = \"D5\"\nglobs = [\"D5.+\"]\n");
        File.WriteAllText(Path.Combine(root, path), source);
        var inspector = PrepareStatementInspector(root);
        RequireSuccess(TestProcessRunner.Run("lake", ["build"], root,
            TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024));

        var compactor = Path.Combine(TestRepositoryLayout.FindRoot(), "tools", "lean-inspector", "materials.py");
        var inputs = Path.Combine(root, "utility.json");
        var output = Path.Combine(root, "report.json");
        File.WriteAllText(inputs, JsonSerializer.Serialize(new[] { new {
            modulePath = path, claimGid, claimModule = module, claimSelector = "claim",
            claimSourcePath = path, claimSourceSha256 = sourceHash,
            resultGid = gid + "." + result, resultModule = module, resultSelector = result,
        } }));
        RequireSuccess(TestProcessRunner.Run("lake", ["env", "lean", "--root=" + Path.GetDirectoryName(inspector), "--run", inspector, "--statements-only",
            "--output", output + ".spool", "--material-spool", output + ".materials",
            "--utility-input", inputs, module, path, sourceHash], root,
            TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024));
        RequireSuccess(TestProcessRunner.Run("python3", [compactor, "compact", output + ".spool", output + ".materials", output, manifest], root,
            TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create([RawRepositoryEntry.FromText(path, source)]))).Snapshot;
        var report = RawLeanReportArtifact.ReadFile(output, snapshot);
        var validation = UtilityDeclarationValidator.Validate(Enum.Parse<UtilityValidationPhase>(phase),
            RepoPath.CreateKnown(path), utility, snapshot, () => report);

        Assert.Equal(valid, validation.IsAccepted);
        if (!valid) Assert.Equal(UtilityValidationFailure.RefutationInvalid, validation.Failure);
        Assert.Equal(valid, report.Files[RepoPath.CreateKnown(path)].Refutation!.IsClosedNegation);
    }

    [Fact]
    public void RealLeanProducesTypedRefutationsAndRejectsPositiveOrConditionalRelabeling()
    {
        using var temporary = new TemporaryDirectory();
        var root = temporary.Path;
        var manifest = Path.Combine(root, LeanReportRegistrationFixture.ManifestPath);
        File.WriteAllText(manifest, LeanReportRegistrationFixture.Manifest);
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
            "name = \"refutation_fixture\"\ndefaultTargets = [\"D5\", \"LeanInformationAudit\"]\n[[lean_lib]]\nname = \"D5\"\nglobs = [\"D5.+\"]\n");
        File.WriteAllText(Path.Combine(root, path), declarations);
        File.WriteAllText(Path.Combine(root, externalPath), externalSource);
        var inspector = PrepareStatementInspector(root);
        RequireSuccess(TestProcessRunner.Run("lake", ["build"], root,
            TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024));

        var compactor = Path.Combine(TestRepositoryLayout.FindRoot(), "tools", "lean-inspector", "materials.py");
        var inputs = Path.Combine(root, "utility.json");
        var output = Path.Combine(root, "report.json");
        foreach (var (result, claim, valid) in new[] {
            ("direct", "proposed_law", true), ("bridged", "proposed_law", true),
            ("conjunction_bridge", "proposed_law", true), ("positive", "proposed_law", false),
            ("witness", "proposed_law", false), ("conditional", "proposed_law", false),
            ("not_a_theorem", "proposed_law", false), ("direct", "other_claim", false),
            ("direct", "parameterized_claim", false), ("general", "proposed_law", false),
            ("direct", "external_law", false),
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
            RequireSuccess(TestProcessRunner.Run("lake", ["env", "lean", "--root=" + Path.GetDirectoryName(inspector), "--run", inspector, "--statements-only",
                "--output", output + ".spool", "--material-spool", output + ".materials",
                "--utility-input", inputs, "D5.S0.Carrier.Probe", path,
                "sha256:" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(source))),
                "D5.S0.Carrier.Law", externalPath,
                "sha256:" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(externalSource)))], root,
                TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024));
            RequireSuccess(TestProcessRunner.Run("python3", [compactor, "compact", output + ".spool", output + ".materials", output, manifest], root,
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
                RequireSuccess(TestProcessRunner.Run("lake", ["env", "lean", "--root=" + Path.GetDirectoryName(inspector), "--run", inspector, "--statements-only",
                    "--output", output + ".subset.spool", "--material-spool", output + ".subset.materials",
                    "--utility-input", inputs, "D5.S0.Carrier.Probe", path,
                    "sha256:" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(source)))], root,
                    TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024));
                RequireSuccess(TestProcessRunner.Run("python3", [compactor, "compact", output + ".subset.spool", output + ".subset.materials",
                    output + ".subset", manifest], root,
                    TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024));
                using var subset = JsonDocument.Parse(FixtureFile.ReadAllBytes(output + ".subset"));
                var modules = subset.RootElement.GetProperty("modules");
                Assert.Equal(1, modules.GetArrayLength());
                Assert.False(modules[0].GetProperty("utility_refutation").GetProperty("is_closed_negation").GetBoolean());
            }
        }
    }

    private static string PrepareStatementInspector(string root)
    {
        var repository = TestRepositoryLayout.FindRoot();
        var producer = Path.Combine(repository, "tools", "lean-inspector");
        foreach (var module in new[] { "RawArtifacts", "CompiledMetadata", "CompiledAxioms", "Contract/SourceAudit" })
        {
            var path = Path.Combine("LeanInformationAudit", module + ".lean");
            var destination = Path.Combine(root, path);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.Copy(Path.Combine(producer, path), destination);
        }
        File.AppendAllText(Path.Combine(root, "lakefile.toml"),
            "[[lean_lib]]\nname = \"LeanInformationAudit\"\nglobs = [\"LeanInformationAudit.+\"]\n");
        File.Copy(Path.Combine(producer, "materials.py"), Path.Combine(root, "materials.py"));
        RequireSuccess(TestProcessRunner.Run("python3", ["-c", """
            import sys
            from pathlib import Path
            producer, root = map(Path, sys.argv[1:])
            sys.path.insert(0, str(producer / 'tests'))
            from test_native_support import transport_inspector
            (root / 'Inspector.lean').write_text(transport_inspector((producer / 'Inspector.lean').read_text()))
            """, producer, root], root, TestBudgets.LeanProcessHangGuard, 8 * 1024 * 1024));
        return Path.Combine(root, "Inspector.lean");
    }

    private static void RequireSuccess(ProcessOutput result)
    {
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
