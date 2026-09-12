using System.IO.Compression;
using System.Text;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using StrataLint.EngineeringScope;
using StrataLint.TestSupport;

namespace StrataLint.Tests;

public sealed class CommonCurrentEvidenceValidationTests
{
    [Theory]
    [InlineData("validate")]
    [InlineData("export")]
    [InlineData("pack")]
    [InlineData("verify")]
    public void EachEntryValidatesSharedReportOnceAndNextEntryValidatesAgain(string entry)
    {
        using var fixture = new EvidenceFixture();
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

    private sealed class EvidenceFixture : IDisposable
    {
        private const string Project = "fixtures/Producer.csproj";
        private const string Source = "D5/S0/Synthetic/Evidence.lean";
        private const string Log = "build/ci/fixture.log";
        private readonly TemporaryDirectory temporary = new();
        private readonly string commit;
        private readonly string retained;
        internal string Root => temporary.Path;
        internal EvidenceFixture()
        {
            Write(Project, "<Project />\n");
            Write(Source, "-- synthetic report input\n");
            Write("global.json", "{\"sdk\":{\"version\":\"10.0.103\"}}\n");
            Write(".gitignore", "build/\n.lake/\n");
            Write(EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Manifest(
                new EngineeringProjectFixture(Project, "Producer", "test-support", false, [])));
            const string producer = "Meta/ReportProducers/fixture.json";
            Write(producer, "{\"schema\":\"report-producer-scope-v1\",\"scripts\":[],\"projects\":[],\"materials\":[\"global.json\"]}");
            var registration = JsonNode.Parse(CommonCheckRegistrationFixture.Manifest(Project))!;
            foreach (var id in new[] { "SL-001", "SL-002" })
                registration["checks"]!.AsArray().Single(row => row!["id"]!.ToString() == id)!["report_inputs"] =
                    JsonNode.Parse("[{\"producer\":\"" + producer + "\",\"artifact\":\"raw-lean-report\",\"materials\":[\"global.json\"]}]");
            Write(CommonExecutionEvidence.CheckManifestPath, registration.ToJsonString());
            Git("init", "-q"); Git("add", ".");
            Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "evidence inputs");
            commit = Git("rev-parse", "HEAD");
            RawLeanReportArtifact.WriteFile(Path.Combine(Root, CommonExecutionEvidence.ReportPath), CommonExecutionEvidence.Snapshot(Root),
                LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
                {
                    [Source] = new([], [new LeanDeclaration("evidence", "def", "Nat", [])]),
                }));
            foreach (var suffix in new[] { ".sha256", ".input.attestation", ".provenance.json", ".seed.json" })
                Write(CommonExecutionEvidence.ReportPath + suffix, "fixture companion\n");
            Write(Log, "fixture build\n");
            var build = CommonExecutionEvidence.SealBuild(Root, CommonExecutionEvidence.Candidate(Root), [Log],
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
        internal void Run(string entry)
        {
            if (entry == "validate") { _ = CommonExecutionEvidence.ValidateCurrent(Root); return; }
            if (entry == "export") { Assert.True(CommonExecutionEvidence.ExportCheckSeed(Root, "current", TextWriter.Null)); return; }
            var arguments = new[] { entry == "pack" ? "transport-pack" : "transport-verify", "--repository", Root,
                "--stage", "current", "--commit", commit, "--run-id", "17", "--run-attempt", "1" };
            if (entry == "pack") arguments = [.. arguments, "--archive", Path.Combine(Root, "build/current.tgz")];
            Assert.Equal(0, CiTransport.Run(arguments, TextWriter.Null));
        }
        internal byte[] Read(string path) => File.ReadAllBytes(Path.Combine(Root, path));
        internal void Damage(string damage)
        {
            var path = damage switch
            {
                "canonical-report" => CommonExecutionEvidence.ReportPath,
                "retained-report" => retained,
                "canonical-material" => CommonExecutionEvidence.ReportPath + ".materials.zip",
                "retained-material" => retained + ".materials.zip",
                "candidate" => Source,
                _ => CommonExecutionEvidence.Read<CommonCheckRecord>(Root, CommonExecutionEvidence.ChecksPath("current")).Units[0].Operations[0].Log,
            };
            File.AppendAllText(Path.Combine(Root, path), "damage");
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
