using System.Formats.Tar;
using System.IO.Compression;
using System.Text;
using StrataLint.EngineeringScope;
using StrataLint.TestSupport;
using File = StrataLint.TestSupport.TemporaryFileSystem.File;
using Directory = StrataLint.TestSupport.TemporaryFileSystem.Directory;

namespace StrataLint.Tests;

public sealed class BuildMaterialHandoffTests
{
    [Theory]
    [InlineData("transport")]
    [InlineData("missing-binary")]
    [InlineData("corrupt-binary")]
    [InlineData("wrong-round")]
    [InlineData("wrong-candidate")]
    public void BuildTransportsSealedBinariesWithoutAnAnalysisHandoff(string scenario)
    {
        var producer = Directory.CreateTempSubdirectory("build-producer-").FullName;
        var recipient = Directory.CreateTempSubdirectory("build-recipient-").FullName;
        try
        {
            File.WriteAllText(Path.Combine(producer, "README.md"), "candidate fixture\n");
            File.WriteAllText(Path.Combine(producer, ".gitignore"), "build/\n");
            Git(producer, "init", "-q");
            Git(producer, "add", ".");
            Git(producer, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "candidate");
            const string binary = "build/runtime/StrataLint.EngineeringScope.dll";
            const string log = "build/ci/fixture.log";
            Directory.CreateDirectory(Path.Combine(producer, "build/runtime"));
            Directory.CreateDirectory(Path.Combine(producer, "build/ci"));
            System.IO.File.Copy(typeof(CommonExecutionEvidence).Assembly.Location, Path.Combine(producer, binary));
            if (!OperatingSystem.IsWindows())
                System.IO.File.SetUnixFileMode(Path.Combine(producer, binary),
                    UnixFileMode.UserRead | UnixFileMode.UserWrite);
            File.WriteAllText(Path.Combine(producer, log), "executed\n");
            var sealedBuild = CommonExecutionEvidence.SealBuild(producer, CommonExecutionEvidence.Candidate(producer), [binary],
                CommonExecutionEvidence.BuildSteps.Select(name => new StageStep(name, 0, 0, "executed", log)).ToArray());
            Assert.Equal(new[] { log, binary }, sealedBuild.Materials.Select(material => material.Path));
            var commit = Git(producer, "rev-parse", "HEAD");
            var archive = Path.Combine(producer, "build", "build.tar.gz");
            Assert.Equal(0, Transport("transport-pack", producer, commit, archive));
            Git(producer, "clone", "--quiet", "--no-hardlinks", producer, recipient);
            using (var compressed = new GZipStream(new MemoryStream(File.ReadAllBytes(archive)), CompressionMode.Decompress))
                TarFile.ExtractToDirectory(compressed, recipient, overwriteFiles: false);
            Directory.Delete(producer, recursive: true);
            Assert.Equal(0, Transport("transport-verify", recipient, commit));
            Assert.Equal(sealedBuild.Materials, CommonExecutionEvidence.ValidateBuild(recipient, sealedBuild.Round).Materials);
            switch (scenario)
            {
                case "missing-binary": File.Delete(Path.Combine(recipient, binary)); break;
                case "corrupt-binary": File.WriteAllText(Path.Combine(recipient, binary), "corrupt binary"); break;
                case "wrong-candidate": File.WriteAllText(Path.Combine(recipient, "README.md"), "different candidate\n"); break;
            }
            if (scenario == "missing-binary")
                Assert.ThrowsAny<IOException>(() => CommonExecutionEvidence.ValidateBuild(recipient));
            else if (scenario != "transport")
                Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateBuild(recipient,
                    scenario == "wrong-round" ? "other-round" : sealedBuild.Round));
        }
        finally
        {
            if (Directory.Exists(producer)) Directory.Delete(producer, recursive: true);
            Directory.Delete(recipient, recursive: true);
        }
    }

    private static int Transport(string command, string root, string commit, string? archive = null) =>
        CiTransport.Run(new[] { command, "--repository", root, "--stage", "build", "--commit", commit,
                "--run-id", "17", "--run-attempt", "2" }
            .Concat(archive is null ? [] : new[] { "--archive", archive }).ToArray(), TextWriter.Null);

    private static string Git(string root, params string[] arguments)
    {
        var result = TestProcessRunner.Run("git", arguments, root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        return Encoding.UTF8.GetString(result.StandardOutput).Trim();
    }
}
