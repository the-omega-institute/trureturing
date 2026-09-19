using System.IO.Compression;
using System.Text;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using StrataLint.EngineeringScope;
using StrataLint.TestSupport;

namespace StrataLint.Tests;

[Collection("CI fixture environment")]
public sealed partial class CommonCurrentEvidenceValidationTests
{
    [Fact]
    public void CurrentCliHandoffReclaimsTemporaryValidationState()
    {
        using var fixture = new EvidenceFixture(currentStage: true);
        using var deadline = new CancellationTokenSource();
        var previous = RawLeanReportArtifact.Reading.Value;
        WeakReference? temporary = null;
        var live = new byte[256 * 1024];
        var liveReference = new WeakReference(live);
        var reads = 0;
        var readsAtHandoff = 0;
        bool? temporaryAlive = null;
        bool? liveAlive = null;
        using var output = new HandoffOutput(() =>
        {
            readsAtHandoff = reads;
            temporaryAlive = temporary?.IsAlive;
            liveAlive = liveReference.IsAlive;
            // Stop at the actual second Step boundary. Child execution and final
            // sealing are exercised by the native-apphost ResourceRouteTests.
            deadline.Cancel();
        });
        try
        {
            RawLeanReportArtifact.Reading.Value = () =>
            {
                if (++reads == 1) temporary = PromotedTemporaryState();
            };
            Assert.Equal(2, fixture.RunCurrent(output, deadline.Token));
        }
        finally { RawLeanReportArtifact.Reading.Value = previous; }
        Assert.Equal(1, readsAtHandoff);
        Assert.Equal(false, temporaryAlive);
        Assert.Equal(true, liveAlive);
        Assert.Equal(1, reads);
        Assert.Contains("PREFLIGHT_BUDGET_EXHAUSTED owner=outer-deadline", output.ToString(), StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.CurrentPath)));
        GC.KeepAlive(live);
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static WeakReference PromotedTemporaryState()
    {
        // The existing read observer cannot expose the reader's private graph.
        // This models dead large preparation state at the actual parent handoff.
        var state = new byte[1024 * 1024];
        var reference = new WeakReference(state);
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
        GC.KeepAlive(state);
        return reference;
    }

    [Theory]
    [InlineData("missing-report", "Could not find file")]
    [InlineData("invalid-report", "Raw Lean report is not valid JSON")]
    [InlineData("canonical-material", "archive")]
    [InlineData("candidate", "source hash")]
    public void CurrentRejectsProducerReportDamageBeforeSecondStep(string damage, string diagnostic)
    {
        using var fixture = new EvidenceFixture(currentStage: true);
        using var output = new StringWriter();
        Assert.Equal(2, fixture.RunCurrent(output, processExited: _ => fixture.Damage(damage)));
        Assert.Contains(diagnostic, output.ToString(), StringComparison.OrdinalIgnoreCase);
        var summary = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "build/ci/current-result.json")))!;
        Assert.Equal("lean-report", Assert.Single(summary["steps"]!.AsArray())!["name"]!.ToString());
        Assert.DoesNotContain("\"name\":\"check-current\"", output.ToString(), StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.CurrentPath)));
    }

    private sealed class HandoffOutput(Action handoff) : StringWriter
    {
        private bool observed;
        public override void Flush()
        {
            base.Flush();
            if (observed || !ToString().Contains("\"name\":\"check-current\"", StringComparison.Ordinal)) return;
            observed = true;
            handoff();
        }
    }

    [Theory]
    [InlineData("validate")]
    [InlineData("export")]
    [InlineData("pack")]
    [InlineData("verify")]
    [InlineData("finalize")]
    public void EachEntryValidatesSharedReportOnceAndNextEntryValidatesAgain(string entry)
    {
        using var fixture = new EvidenceFixture();
        if (entry == "finalize") fixture.Run(entry);
        var current = fixture.Read(CommonExecutionEvidence.CurrentPath);
        var transport = fixture.Read(CiTransport.ManifestPath("current"));
        var previous = RawLeanReportArtifact.Reading.Value;
        var reads = 0;
        try
        {
            RawLeanReportArtifact.Reading.Value = () => reads++;
            fixture.Run(entry);
            Assert.Equal(1, reads);
            fixture.Run(entry);
            Assert.Equal(2, reads);
        }
        finally { RawLeanReportArtifact.Reading.Value = previous; }
        Assert.Equal(current, fixture.Read(CommonExecutionEvidence.CurrentPath));
        Assert.Equal(transport, fixture.Read(CiTransport.ManifestPath("current")));
    }

    [Theory]
    [InlineData("canonical-report")]
    [InlineData("retained-report")]
    [InlineData("canonical-material")]
    [InlineData("retained-material")]
    [InlineData("unit-log")]
    [InlineData("candidate")]
    public void NewValidationRejectsDamageAfterPreviousSuccessfulValidation(string damage)
    {
        using var fixture = new EvidenceFixture();
        fixture.Run("validate");
        fixture.Damage(damage);
        var error = Assert.ThrowsAny<Exception>(() => fixture.Run("validate"));
        Assert.Contains(damage == "candidate" ? "candidate identity" : "artifact integrity mismatch", error.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("validate")]
    [InlineData("export")]
    [InlineData("pack")]
    [InlineData("verify")]
    [InlineData("finalize")]
    public void ResealedRetainedZipStillRequiresStatementMaterialValidation(string entry)
    {
        using var fixture = new EvidenceFixture();
        fixture.Run(entry);
        fixture.CorruptAndResealRetainedZip();
        var error = Assert.ThrowsAny<Exception>(() => fixture.Run(entry));
        Assert.Contains("statement material hash mismatch", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SharedMaterialStillChecksEachUnitsExpectedDigest()
    {
        using var fixture = new EvidenceFixture();
        fixture.ContradictSharedMaterialDigest();
        var error = Assert.Throws<InvalidDataException>(() => fixture.Run("validate"));
        Assert.Contains("artifact integrity mismatch", error.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("canonical-report")]
    [InlineData("retained-report")]
    [InlineData("canonical-material")]
    [InlineData("retained-material")]
    [InlineData("unit-log")]
    [InlineData("candidate")]
    [InlineData("input")]
    [InlineData("round")]
    public void CompletionRevalidatesEvidenceReplacedAfterPreviousValidation(string damage)
    {
        using var fixture = new EvidenceFixture();
        fixture.Run("checks");
        fixture.Damage(damage);
        Assert.ThrowsAny<Exception>(() => fixture.Complete());
    }

    private sealed class EvidenceFixture : IDisposable
    {
        private const string Project = "fixtures/Producer.csproj";
        private const string Source = "D5/S0/Synthetic/Evidence.lean";
        private const string Log = "build/ci/fixture.log";
        private readonly TemporaryDirectory temporary = new();
        private readonly string commit;
        private readonly string retained;
        private readonly CommonStageRecord build;
        internal string Root => temporary.Path;
        internal EvidenceFixture(bool currentStage = false)
        {
            Write(Project, "<Project />\n");
            Write(Source, "-- synthetic report input\n");
            Write("global.json", "{\"sdk\":{\"version\":\"10.0.103\"}}\n");
            Write(".gitignore", "build/\n.lake/\n**/bin/\n");
            if (currentStage)
            {
                Write("Makefile", "lean-report:\n\t@true\n");
                Write(CommonExecutionEvidence.CliPath, "fixture CLI binary");
                Write(CommonExecutionEvidence.LeanProducerPath, "fixture producer binary");
            }
            Write(EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Manifest(
                new EngineeringProjectFixture(Project, "Producer", "test-support", false, [])));
            const string producer = "Meta/ReportProducers/fixture.json";
            const string consumer = "Meta/ReportConsumers/fixture.json";
            Write(producer, "{\"schema\":\"report-producer-scope-v2\",\"registration\":\"lean-report-inputs.json\",\"scope\":\"lean-report\",\"projects\":[]}");
            Write("lean-report-inputs.json", "{\"producer_scopes\":{\"lean-report\":{\"include\":[{\"pattern\":\"global.json\",\"optional\":false}],\"exclude\":[]}}}");
            Write(consumer, System.Text.Json.JsonSerializer.Serialize(new
            {
                schema = "report-consumer-inputs-v1", producer, projects = Array.Empty<string>(), materials = new[] { "global.json" },
            }));
            var registration = JsonNode.Parse(CommonCheckRegistrationFixture.Manifest(Project))!;
            foreach (var id in new[] { "SL-001", "SL-002" })
                registration["checks"]!.AsArray().Single(row => row!["id"]!.ToString() == id)!["report_inputs"] =
                    JsonNode.Parse(System.Text.Json.JsonSerializer.Serialize(new[]
                    {
                        new { producer, consumer, artifact = "raw-lean-report", materials = new[] { "global.json" } },
                    }));
            Write(CommonExecutionEvidence.CheckManifestPath, registration.ToJsonString());
            Git("init", "-q"); Git("add", ".");
            Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "evidence inputs");
            commit = Git("rev-parse", "HEAD");
            RawLeanReportArtifact.WriteFile(Path.Combine(Root, CommonExecutionEvidence.ReportPath), CommonExecutionEvidence.Snapshot(Root),
                LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
                {
                    [Source] = new([], [new LeanDeclaration("evidence", "def", "Nat", [])]),
                }));
            Write(CommonExecutionEvidence.ReportPath + ".sha256", CommonExecutionEvidence.Hash(Path.Combine(Root, CommonExecutionEvidence.ReportPath))
                + "  " + Path.GetFileName(CommonExecutionEvidence.ReportPath) + "\n");
            foreach (var suffix in new[] { ".input.attestation", ".provenance.json" })
                Write(CommonExecutionEvidence.ReportPath + suffix, "fixture companion\n");
            Write(Log, "fixture build\n");
            build = CommonExecutionEvidence.SealBuild(Root, CommonExecutionEvidence.Candidate(Root),
                !currentStage ? [Log] : [Log, CommonExecutionEvidence.CliPath, CommonExecutionEvidence.LeanProducerPath],
                CommonExecutionEvidence.BuildSteps.Select(name => new StageStep(name, 0, 0, "executed", Log)).ToArray());
            var checks = CommonExecutionEvidence.BeginChecks(Root, "current", build, TextWriter.Null);
            foreach (var id in checks.Ids)
                checks.Run(id, () => new([new(id, 0, id.StartsWith("SL-", StringComparison.Ordinal)
                    ? CommonCheckRegistrationFixture.Predicate(id) : "passed")],
                    id == "scribe-describe" ? CommonCheckRegistrationFixture.ScribeMaterial : null));
            var accepted = checks.Seal();
            retained = accepted.Units.First(unit => unit.Report is not null).Report!;
            Assert.Single(accepted.Units.Where(unit => unit.Report is not null).Select(unit => unit.Report).Distinct());
            CommonExecutionEvidence.SealCurrent(Root, build,
                CommonExecutionEvidence.CurrentSteps.Select(name => new StageStep(name, 0, 0, "executed", Log)).ToArray());
            Run("pack");
        }
        internal int RunCurrent(TextWriter output, CancellationToken deadline = default,
            Action<System.Diagnostics.Process>? processExited = null)
        {
            using var environment = new CiFixtureEnvironment();
            return new CommonStages(Root, output, deadline, processExited, seedExport: SeedExportMode.Deferred).Run("current", null);
        }
        internal void Run(string entry)
        {
            if (entry == "checks") { _ = CommonExecutionEvidence.ValidateChecks(Root, "current", build); return; }
            if (entry == "finalize")
            {
                var completed = Complete();
                Assert.Equal(CommonExecutionEvidence.CurrentSteps, completed.Select(step => step.Name));
                return;
            }
            if (entry == "validate") { _ = CommonExecutionEvidence.ValidateCurrent(Root); return; }
            if (entry == "export") { Assert.True(CommonExecutionEvidence.ExportCheckSeed(Root, "current", TextWriter.Null)); return; }
            var arguments = new[] { entry == "pack" ? "transport-pack" : "transport-verify", "--repository", Root,
                "--stage", "current", "--commit", commit, "--run-id", "17", "--run-attempt", "1" };
            if (entry == "pack") arguments = [.. arguments, "--archive", Path.Combine(Root, "build/current.tgz")];
            Assert.Equal(0, CiTransport.Run(arguments, TextWriter.Null));
        }
        internal StageStep[] Complete() => CommonExecutionEvidence.CompleteCurrent(Root, build,
            [new("lean-report", 0, 0, "executed", Log)]);
        internal byte[] Read(string path) => File.ReadAllBytes(Path.Combine(Root, path));
        internal void Damage(string damage)
        {
            if (damage is "missing-report" or "invalid-report")
            {
                var report = Path.Combine(Root, CommonExecutionEvidence.ReportPath);
                if (damage == "missing-report") File.Delete(report);
                else File.WriteAllText(report, "not JSON");
                return;
            }
            if (damage is "input" or "round")
            {
                var checkPath = CommonExecutionEvidence.ChecksPath("current");
                var checks = CommonExecutionEvidence.Read<CommonCheckRecord>(Root, checkPath);
                CommonExecutionEvidence.Write(Root, checkPath, damage == "round" ? checks with { Round = new string('a', 32) }
                    : checks with { Units = checks.Units.Select(unit => unit with { InputFingerprint = new string('0', 64) }).ToArray() });
                return;
            }
            var path = damage switch
            {
                "canonical-report" => CommonExecutionEvidence.ReportPath,
                "retained-report" => retained,
                "canonical-material" => CommonExecutionEvidence.ReportPath + ".materials.zip",
                "retained-material" => retained + ".materials.zip",
                "candidate" => Source,
                _ => CommonExecutionEvidence.Read<CommonCheckRecord>(Root, CommonExecutionEvidence.ChecksPath("current")).Units[0].Operations[0].Log,
            };
            if (damage == "canonical-material") File.WriteAllText(Path.Combine(Root, path), "not a ZIP archive");
            else File.AppendAllText(Path.Combine(Root, path), "damage");
        }
        internal void CorruptAndResealRetainedZip()
        {
            var path = retained + ".materials.zip";
            var full = Path.Combine(Root, path);
            using (var archive = ZipFile.Open(full, ZipArchiveMode.Update))
            {
                var old = Assert.Single(archive.Entries);
                var name = old.FullName;
                old.Delete();
                using var writer = new StreamWriter(archive.CreateEntry(name).Open());
                writer.Write("different statement");
            }
            ExecutionMaterial Reseal(ExecutionMaterial material) => material.Path == path
                ? material with { Sha256 = CommonExecutionEvidence.Hash(full) } : material;
            var checks = CommonExecutionEvidence.Read<CommonCheckRecord>(Root, CommonExecutionEvidence.ChecksPath("current"));
            CommonExecutionEvidence.Write(Root, CommonExecutionEvidence.ChecksPath("current"), checks with
            {
                Units = checks.Units.Select(unit => unit with { Materials = unit.Materials.Select(Reseal).ToArray() }).ToArray(),
            });
            var current = CommonExecutionEvidence.Read<CommonStageRecord>(Root, CommonExecutionEvidence.CurrentPath);
            CommonExecutionEvidence.Write(Root, CommonExecutionEvidence.CurrentPath, current with
            {
                Materials = current.Materials.Select(material => material.Path == CommonExecutionEvidence.ChecksPath("current")
                    ? material with { Sha256 = CommonExecutionEvidence.Hash(Path.Combine(Root, material.Path)) } : Reseal(material)).ToArray(),
            });
        }
        internal void ContradictSharedMaterialDigest()
        {
            var path = CommonExecutionEvidence.ChecksPath("current");
            var checks = CommonExecutionEvidence.Read<CommonCheckRecord>(Root, path);
            CommonExecutionEvidence.Write(Root, path, checks with
            {
                Units = checks.Units.Select(unit => unit.Id != "SL-002" ? unit : unit with
                {
                    Materials = unit.Materials.Select(material => material.Path != retained + ".materials.zip" ? material
                        : material with { Sha256 = new string('0', 64) }).ToArray(),
                }).ToArray(),
            });
            var current = CommonExecutionEvidence.Read<CommonStageRecord>(Root, CommonExecutionEvidence.CurrentPath);
            CommonExecutionEvidence.Write(Root, CommonExecutionEvidence.CurrentPath, current with
            {
                Materials = current.Materials.Select(material => material.Path != path ? material
                    : material with { Sha256 = CommonExecutionEvidence.Hash(Path.Combine(Root, path)) }).ToArray(),
            });
        }
        private void Write(string path, string text)
        {
            var full = Path.Combine(Root, path);
            Directory.CreateDirectory(Path.GetDirectoryName(full)!);
            File.WriteAllText(full, text);
        }
        private string Git(params string[] arguments)
        {
            var result = TestProcessRunner.Run("git", arguments, Root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
            Assert.Equal(0, result.ExitCode);
            return Encoding.UTF8.GetString(result.StandardOutput).Trim();
        }
        public void Dispose() => temporary.Dispose();
    }
}
