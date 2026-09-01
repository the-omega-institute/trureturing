using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class RevertSelfLockProbeScriptTests
{
    private sealed class TargetedCommandFixture : IDisposable
    {
        private const string Digest =
            "sha256:0000000000000000000000000000000000000000000000000000000000000000";
        private readonly TemporaryDirectory temporary = new();
        private readonly string blockers;
        private string control = string.Empty;
        private readonly string controller;
        private readonly string fakeDotnet;
        private readonly string log;
        private readonly string repository;
        private readonly string staging;
        private readonly string targets;
        private readonly string temporaryPath;

        internal TargetedCommandFixture()
        {
            temporaryPath = temporary.Path;
            repository = Path.Combine(temporaryPath, "subject");
            blockers = Path.Combine(temporaryPath, "blockers.json");
            controller = Path.Combine(
                TestRepositoryLayout.FindRoot(),
                "tools", "StrataLint.EngineeringScope", "bin", "Release", "net10.0",
                "StrataLint.EngineeringScope.dll");
            fakeDotnet = Path.Combine(temporaryPath, "targeted-dotnet");
            log = Path.Combine(temporaryPath, "failed.log");
            staging = Path.Combine(temporaryPath, "bundle", ".staging");
            targets = Path.Combine(temporaryPath, "targets.json");
            ScriptHarnessScratch.EnsureDirectory(repository);
            ScriptHarnessScratch.EnsureDirectory(Path.Combine(temporaryPath, "home"));
            InitializeRepository();
            WriteTargets();
            SealControl();
            WriteFakeDotnet();
        }

        internal string Blockers => blockers;
        internal string NormalizedTrx => Path.Combine(staging, "trx", "engineering-000.trx");
        internal string SupervisorResult => Path.Combine(staging, "supervisor-result.json");

        internal ProcessOutput ExtractBlockers(string text)
        {
            ScriptHarnessScratch.WriteScratchText(log, text);
            return RunController(
                "extract-blockers", "--log", log, "--output", blockers);
        }

        internal ProcessOutput RunTargeted() => RunController(
            "run-targeted",
            "--repository", repository,
            "--subject-kind", "synthetic_noop",
            "--targets", targets,
            "--j0-control", control,
            "--staging-bundle", staging,
            "--evaluator-digest", Digest,
            "--dotnet", fakeDotnet);

        internal void MoveHeadToBase() => Git("reset", "--hard", "HEAD^1");

        private void InitializeRepository()
        {
            Git("init", "--template=", "-b", "main");
            Git("config", "--local", "user.name", "Targeted Probe Test");
            Git("config", "--local", "user.email", "targeted-probe@example.invalid");
            Git("config", "--local", "commit.gpgsign", "false");
            Git("config", "--local", "tag.gpgsign", "false");
            Git("config", "--local", "core.hooksPath", "/dev/null");
            ScriptHarnessScratch.WriteScratchText(Path.Combine(repository, "seed.txt"), "seed\n");
            Git("add", "--", "seed.txt");
            Git("commit", "-m", "seed");
            Git("commit", "--allow-empty", "-m", "synthetic no-op");
        }

        private void WriteTargets() => ScriptHarnessScratch.WriteScratchText(
            targets,
            "{\"schema_version\":1,\"required_identities\":["
            + "{\"assembly\":\"Example.Tests\",\"test_id\":\"ExampleTests.Missing\"},"
            + "{\"assembly\":\"Example.Tests\",\"test_id\":\"ExampleTests.Present\"}],"
            + "\"blockers\":[{\"assembly\":\"Example.Tests\","
            + "\"test_id\":\"ExampleTests.Missing\"}]}\n");

        private void SealControl()
        {
            var temporaryControl = Path.Combine(temporaryPath, "j0-control.tmp.json");
            var seal = RunController(
                "seal-j0-control",
                "--repository", repository,
                "--targets", targets,
                "--evaluator-digest", Digest,
                "--output", temporaryControl);
            Assert.True(seal.ExitCode == 0, Diagnostics(seal));
            var digest = RunController("artifact-digest", "--path", temporaryControl);
            Assert.True(digest.ExitCode == 0, Diagnostics(digest));
            control = Path.Combine(
                temporaryPath,
                Encoding.UTF8.GetString(digest.StandardOutput).Trim()[7..] + ".j0-control.json");
            ScriptHarnessScratch.MoveScratchFile(temporaryControl, control);
        }

        private void WriteFakeDotnet() => ScriptHarnessScratch.WriteExecutableStub(
            fakeDotnet,
            "results=''\n"
            + "while (( $# > 0 )); do\n"
            + "  if [[ \"$1\" == --results-directory ]]; then results=\"$2\"; shift 2; else shift; fi\n"
            + "done\n"
            + "test -n \"$results\"\n"
            + "mkdir -p \"$results\"\n"
            + "printf '%s\\n' '<TestRun><Results><UnitTestResult testId=\"1\" "
            + "testName=\"ExampleTests.Present\" outcome=\"Passed\" /></Results>"
            + "<TestDefinitions><UnitTest id=\"1\" storage=\"example.tests.dll\">"
            + "<TestMethod className=\"ExampleTests\" name=\"Present\" /></UnitTest>"
            + "</TestDefinitions><ResultSummary><Counters total=\"1\" executed=\"1\" "
            + "passed=\"1\" /></ResultSummary></TestRun>' > \"$results/targeted.trx\"");

        private ProcessOutput RunController(params string[] arguments) => TestProcessRunner.Run(
            "/usr/bin/env",
            [
                "-u", "GIT_AUTHOR_NAME", "-u", "GIT_AUTHOR_EMAIL",
                "-u", "GIT_COMMITTER_NAME", "-u", "GIT_COMMITTER_EMAIL",
                "-u", "GIT_CONFIG", "-u", "GIT_CONFIG_PARAMETERS", "-u", "GIT_TEMPLATE_DIR",
                $"HOME={Path.Combine(temporaryPath, "home")}",
                "GIT_CONFIG_GLOBAL=/dev/null", "GIT_CONFIG_SYSTEM=/dev/null",
                "GIT_CONFIG_NOSYSTEM=1", "GIT_CONFIG_COUNT=0",
                "dotnet", controller, "self-lock-probe", .. arguments,
            ],
            temporaryPath,
            TestBudgets.ScriptProcessHangGuard,
            512 * 1024);

        private void Git(params string[] arguments)
        {
            var result = TestProcessRunner.Run(
                "/usr/bin/env",
                [
                    "-u", "GIT_AUTHOR_NAME", "-u", "GIT_AUTHOR_EMAIL",
                    "-u", "GIT_COMMITTER_NAME", "-u", "GIT_COMMITTER_EMAIL",
                    "-u", "GIT_CONFIG", "-u", "GIT_CONFIG_PARAMETERS", "-u", "GIT_TEMPLATE_DIR",
                    $"HOME={Path.Combine(temporaryPath, "home")}",
                    "GIT_CONFIG_GLOBAL=/dev/null", "GIT_CONFIG_SYSTEM=/dev/null",
                    "GIT_CONFIG_NOSYSTEM=1", "GIT_CONFIG_COUNT=0",
                    "/usr/bin/git", "-C", repository, .. arguments,
                ],
                repository,
                TestBudgets.ScriptProcessHangGuard,
                64 * 1024);
            Assert.True(result.ExitCode == 0, Diagnostics(result));
        }

        public void Dispose() => temporary.Dispose();
    }
}
