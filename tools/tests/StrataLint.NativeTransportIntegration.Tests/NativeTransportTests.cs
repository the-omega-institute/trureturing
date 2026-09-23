using StrataLint.EngineeringScope;
using static StrataLint.TestSupport.TransportFixture;
using static StrataLint.TestSupport.NativeReportFixture;
using static StrataLint.TestSupport.ExecutionFixture;
using System.Diagnostics;
using System.Formats.Tar;
using System.IO.Compression;
using System.Security.Cryptography;
using System.Text.Json;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.NativeTransportIntegration.Tests;

[Collection("Native transport process boundary")]
public sealed class NativeTransportTests
{
    [Fact]
    public void CurrentCliTransportRoundTripRetainsRegistrationAndRejectsInvalidBundles()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ExecutionFixture();
        Prepare(fixture, current: false);
        var root = fixture.Root;
        var repository = TestRepositoryLayout.FindRoot();
        var runtime = Path.GetDirectoryName(CommonExecutionEvidence.RunnerPath)!;
        Directory.CreateDirectory(Path.Combine(root, runtime));
        var binaries = Directory.GetFiles(Path.Combine(repository, runtime)).Select(file =>
        {
            var relative = runtime + "/" + Path.GetFileName(file);
            File.Copy(file, Path.Combine(root, relative));
            return relative;
        }).ToArray();
        SealEngineering(root, CommonExecutionEvidence.Candidate(root), binaries, Steps(CommonExecutionEvidence.EngineeringSteps));
        Report(root);
        CheckEvidenceFixture.Seal(root, "current", CommonExecutionEvidence.ValidateBuild(root));
        CommonExecutionEvidence.SealCurrent(root, CommonExecutionEvidence.ValidateBuild(root), Steps(CommonExecutionEvidence.CurrentSteps));
        var commit = Git(root, "rev-parse", "HEAD");
        var archive = Path.Combine(root, "build/current.tgz");
        var packed = Cli("pack", root, archive);
        Assert.True(packed.Exit == 0, packed.Text);
        Assert.Contains("status=packed", packed.Text);

        var target = Path.Combine(root, "build/destination");
        Git(root, "clone", "--quiet", "--no-hardlinks", root, target);
        var restored = Cli("restore", target, archive);
        Assert.True(restored.Exit == 0, restored.Text);
        Assert.Contains("status=verified", restored.Text);
        Assert.Equal(File.ReadAllBytes(Path.Combine(root, "Meta/ci-checks.json")),
            File.ReadAllBytes(Path.Combine(target, "Meta/ci-checks.json")));
        Assert.Contains(CommonExecutionEvidence.ValidateCurrent(target).Materials, material => material.Path == "Meta/ci-checks.json");
        Assert.Equal(File.GetUnixFileMode(Path.Combine(root, Log)), File.GetUnixFileMode(Path.Combine(target, Log)));

        foreach (var defect in new[] { "extra", "extra-meta", "escape", "absolute", "symlink", "hardlink", "mode", "hash", "candidate", "round", "missing-registration" })
        {
            var damaged = Path.Combine(root, "build/" + defect + ".tgz");
            using (var input = new GZipStream(File.OpenRead(archive), CompressionMode.Decompress))
            using (var reader = new TarReader(input))
            using (var output = new GZipStream(File.Create(damaged), CompressionLevel.Fastest))
            using (var writer = new TarWriter(output))
            {
                while (reader.GetNextEntry(copyData: true) is { } entry)
                {
                    if (defect == "missing-registration" && entry.Name == "Meta/ci-checks.json") continue;
                    if (entry.Name == Log && defect == "mode") entry.Mode ^= UnixFileMode.UserExecute;
                    if (entry.Name == Log && defect == "hash")
                        entry = new PaxTarEntry(TarEntryType.RegularFile, entry.Name) { Mode = entry.Mode,
                            ModificationTime = entry.ModificationTime, DataStream = new MemoryStream("corrupt"u8.ToArray()) };
                    if (entry.Name == CommonExecutionEvidence.CurrentPath && defect is "candidate" or "round")
                    {
                        var record = CommonExecutionEvidence.Read<CommonStageRecord>(root, CommonExecutionEvidence.CurrentPath);
                        var node = System.Text.Json.Nodes.JsonNode.Parse(File.ReadAllText(Path.Combine(root, entry.Name)))!;
                        node[defect] = defect == "candidate" ? new string('a', 64) : record.Round + "-stale";
                        entry.DataStream = new MemoryStream(System.Text.Encoding.UTF8.GetBytes(node.ToJsonString()));
                    }
                    writer.WriteEntry(entry);
                }
                var extra = defect switch { "extra" => "build/ci/undeclared", "extra-meta" => "Meta/undeclared.json",
                    "escape" => "../escaped", "absolute" => "/escaped", "symlink" or "hardlink" => "build/ci/link", _ => null };
                if (extra is not null)
                {
                    var type = defect == "symlink" ? TarEntryType.SymbolicLink : defect == "hardlink" ? TarEntryType.HardLink : TarEntryType.RegularFile;
                    var entry = new PaxTarEntry(type, extra);
                    if (type == TarEntryType.RegularFile) entry.DataStream = new MemoryStream("extra"u8.ToArray());
                    else entry.LinkName = Log;
                    writer.WriteEntry(entry);
                }
            }
            var rejected = Cli("restore", target, damaged);
            Assert.True(rejected.Exit == 2, defect + ": " + rejected.Text);
            Assert.DoesNotContain("status=verified", rejected.Text);
            Assert.False(File.Exists(Path.Combine(target, "build/ci/undeclared")));
            var recovered = Cli("restore", target, archive);
            Assert.True(recovered.Exit == 0, recovered.Text);
        }
        foreach (var (wrongCommit, run, attempt) in new[] { (commit, "18", "2"), (commit, "17", "3"), (new string('a', 40), "17", "2") })
        {
            var rejected = Cli("verify", target, archive, wrongCommit, run, attempt);
            Assert.True(rejected.Exit == 2, rejected.Text);
        }

        (int Exit, string Text) Cli(string command, string destination, string bundle, string? candidate = null, string run = "17", string attempt = "2") =>
            EngineeringProcess.Process(destination, "python3", ["-B", Path.Combine(repository, "tools/scripts/workflow/ci.py"),
                command, "--repository", destination, "--stage", "current", "--commit", candidate ?? commit,
                "--run-id", run, "--run-attempt", attempt, "--archive", bundle], hangGuard: TestBudgets.WorkflowProcessHangGuard);
    }

}
