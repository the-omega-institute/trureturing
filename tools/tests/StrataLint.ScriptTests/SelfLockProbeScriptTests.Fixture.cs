using System.Collections.Concurrent;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Tests;

[System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
public sealed partial class SelfLockProbeScriptTests
{
    private const string ExpectedAssembly = "Engineering.Tests";
    private const string ExpectedTest = "Engineering.Tests.RequiredIdentity";
    private const string PresentTest = "Engineering.Tests.PresentIdentity";
    private static readonly JsonSerializerOptions JsonOptions = new()
    {
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
    };

    private static ProbeResult ParseResult(ProcessOutput output)
    {
        Assert.NotEmpty(output.StandardOutput);
        return JsonSerializer.Deserialize<ProbeResult>(output.StandardOutput, JsonOptions)
            ?? throw new InvalidOperationException("probe result was empty");
    }

    private static void AssertDecision(
        ProcessOutput output,
        string decision,
        int exitCode)
    {
        Assert.True(output.ExitCode == exitCode, Diagnostics(output));
        Assert.Empty(output.StandardError);
        var result = ParseResult(output);
        Assert.Equal(1, result.SchemaVersion);
        Assert.Equal(decision, result.Decision);
        Assert.False(result.Authorization.ChangesGateStatus);
        Assert.True(result.Authorization.RerunRequiredAfterDevPush);
    }

    private sealed class ProbeFixture : IDisposable
    {
        private static readonly ConcurrentDictionary<(string Path, bool MergeShapedNoop),
            Lazy<ProbeTemplate>> Templates = new();
        private static readonly string ProtectionPolicy = """
            internal static class BootstrapProtectionPolicy
            {
                internal static object Matchers => new[]
                {
                    Atom("tools", ProtectionMatchKind.Prefix, "tools/"),
                    Atom("workflows", ProtectionMatchKind.Prefix, "{workflow-prefix}"),
                };
            }
            """.Replace("{workflow-prefix}", ".github/" + "work" + "flows/", StringComparison.Ordinal);
        private const string ProtectionPolicyPath =
            "tools/StrataLint.Engine/Admission/BootstrapProtectionPolicy.cs";
        private readonly TemporaryDirectory temporary = new();

        internal ProbeFixture(
            string candidatePath = "tools/policy-under-test.txt",
            bool mergeShapedNoop = false)
        {
            var template = Templates.GetOrAdd(
                (candidatePath, mergeShapedNoop),
                static key => new Lazy<ProbeTemplate>(
                    () => new ProbeTemplate(key.Path, key.MergeShapedNoop),
                    LazyThreadSafetyMode.ExecutionAndPublication)).Value;
            CopyDirectory(template.Root, temporary.Path);
            CandidateRepository = Path.Combine(temporary.Path, "candidate");
            J1Repository = Path.Combine(temporary.Path, "j1");
            J0Repository = Path.Combine(temporary.Path, "j0");
            TargetBaseSha = template.TargetBaseSha;
            TargetMergeSha = template.TargetMergeSha;
            ControllerDigest = template.ControllerDigest;
            J1Bundle = new EvidenceBundle(
                Path.Combine(temporary.Path, "j1-bundle"),
                J1Repository,
                "merge",
                ControllerDigest);
            J0Bundle = new EvidenceBundle(
                Path.Combine(temporary.Path, "j0-bundle"),
                J0Repository,
                "synthetic_noop",
                ControllerDigest);
        }

        internal string CandidateRepository { get; }
        internal string ControllerDigest { get; }
        internal EvidenceBundle J0Bundle { get; }
        internal string J0Repository { get; }
        internal EvidenceBundle J1Bundle { get; }
        internal string J1Repository { get; }
        internal string TargetBaseSha { get; }
        internal string TargetMergeSha { get; }

        internal void WriteCandidateMarker(string relativePath, string content)
        {
            var path = Path.Combine(CandidateRepository, relativePath);
            ScriptHarnessScratch.EnsureDirectory(Path.GetDirectoryName(path)!);
            ScriptHarnessScratch.WriteScratchText(path, content);
        }

        private static string CloneAt(string root, string candidateRepository, string name)
        {
            var path = Path.Combine(root, name);
            GitAt(root, "clone", candidateRepository, path);
            ConfigureSyntheticRepository(
                path,
                "Self Lock Test",
                "self-lock@example.invalid");
            return path;
        }

        private static void CopyDirectory(string sourcePath, string targetPath)
        {
            var result = TestProcessRunner.Run(
                "/bin/cp",
                ["-R", sourcePath + "/.", targetPath],
                targetPath,
                TestBudgets.ScriptProcessHangGuard,
                64 * 1024);
            if (result.ExitCode != 0)
            {
                throw new InvalidOperationException(Diagnostics(result));
            }
        }

        private sealed class ProbeTemplate
        {
            private readonly TemporaryDirectory temporary = new();

            internal ProbeTemplate(string candidatePath, bool mergeShapedNoop)
            {
                var candidateRepository = Path.Combine(temporary.Path, "candidate");
                ScriptHarnessScratch.EnsureDirectory(candidateRepository);
                GitAt(candidateRepository, "init", "--template=", "-b", "main");
                ConfigureSyntheticRepository(
                    candidateRepository,
                    "Self Lock Test",
                    "self-lock@example.invalid");
                var before = candidatePath == ProtectionPolicyPath
                    ? ProtectionPolicy
                    : "before\n";
                var after = candidatePath == ProtectionPolicyPath
                    ? ProtectionPolicy + "\n// changed by target merge\n"
                    : "after\n";
                var candidateContent = candidatePath == ProtectionPolicyPath
                    ? after + "\n// changed by candidate\n"
                    : "candidate\n";
                if (candidatePath != ProtectionPolicyPath)
                {
                    CommitFile(
                        candidateRepository,
                        "canonical policy",
                        ProtectionPolicyPath,
                        ProtectionPolicy);
                }
                CommitFile(candidateRepository, "seed", candidatePath, before);
                TargetBaseSha = GitTextAt(candidateRepository, "rev-parse", "HEAD");

                GitAt(candidateRepository, "checkout", "-b", "feature");
                CommitFile(candidateRepository, "gate change", candidatePath, after);
                var feature = GitTextAt(candidateRepository, "rev-parse", "HEAD");
                GitAt(candidateRepository, "checkout", "main");
                TargetMergeSha = CommitTree(
                    candidateRepository,
                    feature,
                    [TargetBaseSha, feature],
                    "merge gate change");
                UpdateMain(candidateRepository, TargetMergeSha, TargetBaseSha);

                GitAt(candidateRepository, "checkout", "-b", "candidate");
                CommitFile(candidateRepository, "candidate change", candidatePath, candidateContent);
                var candidate = GitTextAt(candidateRepository, "rev-parse", "HEAD");
                GitAt(candidateRepository, "checkout", "main");
                var candidateMerge = CommitTree(
                    candidateRepository,
                    candidate,
                    [TargetMergeSha, candidate],
                    "merge candidate change");
                UpdateMain(candidateRepository, candidateMerge, TargetMergeSha);

                var j1Repository = CloneAt(temporary.Path, candidateRepository, "j1");
                GitAt(j1Repository, "checkout", "--detach", TargetMergeSha);
                var j0Repository = CloneAt(temporary.Path, candidateRepository, "j0");
                GitAt(j0Repository, "checkout", "--detach", TargetBaseSha);
                var noopParents = mergeShapedNoop
                    ? new[] { TargetBaseSha, feature }
                    : new[] { TargetBaseSha };
                var noop = CommitTree(
                    j0Repository,
                    TargetBaseSha,
                    noopParents,
                    "synthetic no-op");
                GitAt(j0Repository, "checkout", "--detach", noop);
                ControllerDigest = ReadControllerDigest();
            }

            internal string ControllerDigest { get; }
            internal string Root => temporary.Path;
            internal string TargetBaseSha { get; }
            internal string TargetMergeSha { get; }
        }

        private static void CommitFile(
            string repository,
            string message,
            string relativePath,
            string content)
        {
            var blob = GitTextWithInputAt(repository, content, "hash-object", "-w", "--stdin");
            GitAt(repository, "update-index", "--add", "--cacheinfo", $"100644,{blob},{relativePath}");
            GitAt(repository, "commit", "-m", message);
            GitAt(repository, "reset", "--hard", "HEAD");
        }

        private static string CommitTree(
            string repository,
            string treeSource,
            IReadOnlyList<string> parents,
            string message)
        {
            var arguments = new List<string>
            {
                "commit-tree",
                GitTextAt(repository, "rev-parse", treeSource + "^{tree}"),
            };
            foreach (var parent in parents)
            {
                arguments.Add("-p");
                arguments.Add(parent);
            }
            arguments.Add("-m");
            arguments.Add(message);
            return GitTextAt(repository, arguments.ToArray());
        }

        private static void UpdateMain(string repository, string commit, string previous)
        {
            GitAt(repository, "update-ref", "refs/heads/main", commit, previous);
            GitAt(repository, "reset", "--hard", commit);
        }

        public void Dispose()
        {
            J1Bundle.DeleteAuthorityReceipt();
            J0Bundle.DeleteAuthorityReceipt();
            temporary.Dispose();
        }
    }

    private sealed class EvidenceBundle
    {
        private readonly string repository;

        internal EvidenceBundle(
            string path,
            string repository,
            string subjectKind,
            string evaluatorDigest)
        {
            Path = path;
            this.repository = repository;
            TrxText = CompleteTrx([PresentTest]);
            Supervisor = CreateSupervisor(subjectKind, evaluatorDigest);
            Publish();
        }

        internal string AuthorityReceiptPath { get; private set; } = string.Empty;
        private string currentPayloadPath = string.Empty;
        internal string Path { get; private set; }
        internal JsonObject Supervisor { get; set; }
        internal string TrxText { get; set; }

        internal void Publish()
        {
            var staging = System.IO.Path.Combine(Path, ".staging");
            ScriptHarnessScratch.EnsureDirectory(System.IO.Path.Combine(staging, "trx"));
            var trxPath = System.IO.Path.Combine(staging, "trx", "engineering.trx");
            ScriptHarnessScratch.WriteScratchText(trxPath, TrxText);
            var trxDigest = DigestFile(trxPath);
            Supervisor["trx_artifacts"] = new JsonArray(new JsonObject
            {
                ["file_name"] = "engineering.trx",
                ["assembly"] = ExpectedAssembly,
                ["sha256"] = trxDigest,
            });
            var supervisorPath = System.IO.Path.Combine(staging, "supervisor-result.json");
            ScriptHarnessScratch.WriteScratchText(
                supervisorPath,
                Supervisor.ToJsonString(JsonOptions));
            var publication = PublishBundle(Path, staging);
            AuthorityReceiptPath = publication.AuthorityReceiptPath;
            currentPayloadPath = publication.PayloadPath;
        }

        internal void WriteRawSupervisorAndBind(string json)
        {
            var staging = System.IO.Path.Combine(Path, ".staging");
            ScriptHarnessScratch.EnsureDirectory(System.IO.Path.Combine(staging, "trx"));
            var supervisorPath = System.IO.Path.Combine(staging, "supervisor-result.json");
            ScriptHarnessScratch.WriteScratchText(supervisorPath, json);
            var trxPath = System.IO.Path.Combine(staging, "trx", "engineering.trx");
            ScriptHarnessScratch.WriteScratchText(trxPath, TrxText);
            var publication = PublishBundle(Path, staging);
            AuthorityReceiptPath = publication.AuthorityReceiptPath;
            currentPayloadPath = publication.PayloadPath;
        }

        internal void RemoveFinalizationSentinel() =>
            ScriptHarnessScratch.DeleteScratchFile(
                System.IO.Path.Combine(CurrentPayloadPath(), "finalization.sentinel"));

        internal void RemoveTrxFile() =>
            ScriptHarnessScratch.DeleteScratchFile(
                System.IO.Path.Combine(CurrentPayloadPath(), "trx", "engineering.trx"));

        internal void CorruptTrxWithoutRebinding() =>
            ScriptHarnessScratch.AppendScratchText(
                System.IO.Path.Combine(CurrentPayloadPath(), "trx", "engineering.trx"),
                "<!-- stale cache -->");

        internal void CopyToUnreceiptedPath(string copiedPath)
        {
            var result = TestProcessRunner.Run(
                "/bin/cp",
                ["-R", Path, copiedPath],
                System.IO.Path.GetDirectoryName(Path)!,
                TestBudgets.ScriptProcessHangGuard,
                64 * 1024);
            Assert.True(result.ExitCode == 0, Diagnostics(result));
            Path = copiedPath;
        }

        internal void TamperAuthorityProducerDigest()
        {
            TamperReceiptProducer(AuthorityReceiptPath);
        }

        internal void TamperPublicationSentinelDigest()
        {
            TamperPointerSentinel(System.IO.Path.Combine(Path, "publication.json"));
        }

        internal void DeleteAuthorityReceipt()
        {
            if (AuthorityReceiptPath.Length != 0)
            {
                ScriptHarnessScratch.DeleteScratchFile(AuthorityReceiptPath);
            }
        }

        private string CurrentPayloadPath() => currentPayloadPath;

        private JsonObject CreateSupervisor(string subjectKind, string evaluatorDigest) => new()
        {
            ["schema_version"] = 1,
            ["publication"] = "atomic",
            ["gate"] = "engineering",
            ["subject"] = new JsonObject
            {
                ["kind"] = subjectKind,
                ["head_sha"] = GitTextAt(repository, "rev-parse", "HEAD"),
                ["base_sha"] = GitTextAt(repository, "rev-parse", "HEAD^1"),
                ["head_tree_sha"] = GitTextAt(repository, "rev-parse", "HEAD^{tree}"),
                ["base_tree_sha"] = GitTextAt(repository, "rev-parse", "HEAD^1^{tree}"),
            },
            ["evaluator_digest"] = evaluatorDigest,
            ["termination"] = new JsonObject
            {
                ["kind"] = "exited",
                ["exit_code"] = 1,
                ["signal"] = null,
            },
            ["diagnostics_complete"] = true,
            ["failure_keys"] = new JsonArray("ENGINEERING_TEST_EVIDENCE_FAILED"),
            ["required_identities"] = new JsonArray(
                Identity(ExpectedTest),
                Identity(PresentTest)),
            ["blockers"] = new JsonArray(Blocker(ExpectedTest)),
            ["trx_artifacts"] = new JsonArray(),
            ["diagnostics"] = new JsonArray(),
            ["step_failures"] = new JsonArray(),
        };

        internal static JsonObject Identity(string testId) => new()
        {
            ["assembly"] = ExpectedAssembly,
            ["test_id"] = testId,
        };

        internal static JsonObject Blocker(string testId) => new()
        {
            ["kind"] = "missing_identity",
            ["failure_key"] = "ENGINEERING_TEST_EVIDENCE_FAILED",
            ["assembly"] = ExpectedAssembly,
            ["test_id"] = testId,
        };
    }

    private static void GitAt(string repository, params string[] arguments)
    {
        var result = TestProcessRunner.Run(
            "/usr/bin/env",
            IsolatedGitArguments(arguments),
            repository,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
        Assert.True(result.ExitCode == 0, Diagnostics(result));
    }

    private static string GitTextAt(string repository, params string[] arguments)
    {
        var result = TestProcessRunner.Run(
            "/usr/bin/env",
            IsolatedGitArguments(arguments),
            repository,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
        Assert.True(result.ExitCode == 0, Diagnostics(result));
        return Encoding.UTF8.GetString(result.StandardOutput).Trim();
    }

    private static string GitTextWithInputAt(
        string repository,
        string input,
        params string[] arguments)
    {
        var result = TestProcessRunner.Run(
            "/usr/bin/env",
            IsolatedGitArguments(arguments),
            repository,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024,
            Encoding.UTF8.GetBytes(input));
        Assert.True(result.ExitCode == 0, Diagnostics(result));
        return Encoding.UTF8.GetString(result.StandardOutput).Trim();
    }

    private static void ConfigureSyntheticRepository(
        string repository,
        string userName,
        string userEmail)
    {
        GitAt(repository, "config", "--local", "user.name", userName);
        GitAt(repository, "config", "--local", "user.email", userEmail);
        GitAt(repository, "config", "--local", "commit.gpgsign", "false");
        GitAt(repository, "config", "--local", "tag.gpgsign", "false");
        GitAt(repository, "config", "--local", "core.autocrlf", "false");
        GitAt(repository, "config", "--local", "core.safecrlf", "false");
        GitAt(repository, "config", "--local", "core.hooksPath", "/dev/null");
        GitAt(repository, "config", "--local", "gc.auto", "0");
        GitAt(repository, "config", "--local", "maintenance.auto", "false");
    }

    private static string[] IsolatedGitArguments(IEnumerable<string> arguments) =>
    [
        "-u", "GIT_AUTHOR_NAME",
        "-u", "GIT_AUTHOR_EMAIL",
        "-u", "GIT_COMMITTER_NAME",
        "-u", "GIT_COMMITTER_EMAIL",
        "-u", "GIT_CONFIG",
        "-u", "GIT_CONFIG_PARAMETERS",
        "-u", "GIT_TEMPLATE_DIR",
        "GIT_CONFIG_GLOBAL=/dev/null",
        "GIT_CONFIG_SYSTEM=/dev/null",
        "GIT_CONFIG_NOSYSTEM=1",
        "GIT_CONFIG_COUNT=0",
        "/usr/bin/git",
        .. arguments,
    ];

    private static string Diagnostics(ProcessOutput result) =>
        "stdout:\n" + Encoding.UTF8.GetString(result.StandardOutput)
        + "\nstderr:\n" + Encoding.UTF8.GetString(result.StandardError);
}
