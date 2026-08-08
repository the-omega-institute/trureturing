using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DepositCoverWorkflowScriptTests
{
    [Fact]
    public void DepositCreatesTwoCommitsWithFreezeAndReceiptInTheSecondCommit()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        var before = fixture.CommitCount();

        var result = fixture.Run("deposit");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Equal(before + 2, fixture.CommitCount());
        Assert.Equal(1, fixture.FreezeCount());
        Assert.True(File.Exists(fixture.ReceiptPath));
        Assert.Empty(fixture.Status());
        Assert.Equal(
            [
                "make:lean-report",
                "make:emit",
                "make:echo-residual-summary BASE=synthetic-base",
                "make:emit-check BASE=synthetic-base",
                "dotnet:emit-formalization-receipt",
                "dotnet:ledger-append",
                "make:lean-report",
                "make:echo-residual-summary BASE=synthetic-base",
                "make:emit-check BASE=synthetic-base",
            ],
            fixture.CallKinds());

        var phaseA = fixture.CommitPaths("HEAD~1");
        Assert.Contains(TransactionFixture.LeanPath, phaseA);
        Assert.Contains(TransactionFixture.DefinitionPath, phaseA);
        Assert.Contains(TransactionFixture.EmissionPath, phaseA);
        Assert.Contains(TransactionFixture.EchoPath, phaseA);
        Assert.DoesNotContain(TransactionFixture.LedgerPath, phaseA);
        Assert.DoesNotContain(TransactionFixture.ReceiptRelativePath, phaseA);

        var phaseB = fixture.CommitPaths("HEAD");
        Assert.Contains(
            phaseB,
            path => path.StartsWith(TransactionFixture.LedgerPath + "/", StringComparison.Ordinal));
        Assert.Contains(TransactionFixture.ReceiptRelativePath, phaseB);
    }

    [Fact]
    public void DepositReentryAfterInterruptedFreezeDoesNotAppendASecondFreeze()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        fixture.FailAfterNextFreeze();
        var before = fixture.CommitCount();

        var interrupted = fixture.Run("deposit");
        Assert.NotEqual(0, interrupted.ExitCode);
        Assert.Equal(before + 1, fixture.CommitCount());
        Assert.Equal(1, fixture.FreezeCount());
        Assert.False(File.Exists(fixture.ReceiptPath));

        var resumed = fixture.Run("deposit");

        Assert.True(resumed.ExitCode == 0, Diagnostics(resumed));
        Assert.Equal(before + 2, fixture.CommitCount());
        Assert.Equal(1, fixture.FreezeCount());
        Assert.Equal(1, fixture.CallKinds().Count(call => call == "dotnet:ledger-append"));
        Assert.True(File.Exists(fixture.ReceiptPath));
        Assert.Empty(fixture.Status());
    }

    [Fact]
    public void DepositReentryWithAlignedReceiptKeepsTheOriginalTwoCommitBoundary()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        fixture.FailAfterNextFreeze();
        var before = fixture.CommitCount();
        Assert.NotEqual(0, fixture.Run("deposit").ExitCode);
        fixture.WriteAlignedReceipt();

        var resumed = fixture.Run("deposit");

        Assert.True(resumed.ExitCode == 0, Diagnostics(resumed));
        Assert.Equal(before + 2, fixture.CommitCount());
        Assert.Equal(1, fixture.FreezeCount());
        Assert.Equal(1, fixture.CallKinds().Count(call => call == "dotnet:ledger-append"));
        Assert.Empty(fixture.Status());
    }

    [Fact]
    public void DepositAfterFreezeAndRevokeAppendsANewFreeze()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        fixture.WriteFreezeThenRevoke();

        var result = fixture.Run("deposit");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Equal(1, fixture.CallKinds().Count(call => call == "dotnet:ledger-append"));
        Assert.Equal(2, fixture.FreezeCount());
    }

    [Fact]
    public void DepositDoesNotSkipAFreezeForStaleModuleIdentity()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        fixture.WriteActiveFreeze(
            "git-sha1:0000000000000000000000000000000000000000");

        var result = fixture.Run("deposit");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Equal(1, fixture.CallKinds().Count(call => call == "dotnet:ledger-append"));
        Assert.Equal(2, fixture.FreezeCount());
    }

    [Fact]
    public void DepositRemovesInterruptedTemporaryFilesBeforeStaging()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        fixture.LeaveInterruptedTemporaryFiles();

        var result = fixture.Run("deposit");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.DoesNotContain(fixture.TrackedPaths(), path =>
            path.Contains(".tmp.", StringComparison.Ordinal));
        Assert.Empty(fixture.Status());
    }

    [Fact]
    public void DepositPreservesCanonicalEchoWhenProjectionFailsMidWrite()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        var before = File.ReadAllBytes(Path.Combine(fixture.Root, TransactionFixture.EchoPath));

        var result = fixture.Run("deposit", failEcho: true);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Equal(before, File.ReadAllBytes(Path.Combine(fixture.Root, TransactionFixture.EchoPath)));
        Assert.Equal(0, fixture.FreezeCount());
        Assert.DoesNotContain("dotnet:ledger-append", fixture.CallKinds());
    }

    [Fact]
    public void DepositFailsClosedWhenLeanReportRemainsStale()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();

        var result = fixture.Run("deposit", staleReport: true);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("STALE_LEAN_REPORT", Encoding.UTF8.GetString(result.StandardError), StringComparison.Ordinal);
        Assert.Equal(["make:lean-report", "make:emit"], fixture.CallKinds());
        Assert.Equal(0, fixture.FreezeCount());
    }

    [Fact]
    public void DepositValidatesTheCanonicalReceiptBeforeAppendingFreeze()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();

        var result = fixture.Run("deposit", invalidReceipt: true);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(
            "FORMALIZATION_RECEIPT_INVALID synthetic canonical rejection",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
        Assert.DoesNotContain("dotnet:ledger-append", fixture.CallKinds());
        Assert.Equal(0, fixture.FreezeCount());
    }

    [Fact]
    public void CoverReemitsBeforeAndAfterReceiptAlignmentThenCommitsOnce()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        var deposit = fixture.Run("deposit");
        Assert.True(deposit.ExitCode == 0, Diagnostics(deposit));
        fixture.ClearCalls();
        var before = fixture.CommitCount();

        var result = fixture.Run("cover");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Equal(before + 1, fixture.CommitCount());
        Assert.Equal(
            [
                "make:lean-report",
                "dotnet:cover-atom",
                "make:emit",
                "dotnet:align-scribe-receipt",
                "make:emit",
                "make:echo-residual-summary BASE=synthetic-base",
                "make:emit-check BASE=synthetic-base",
            ],
            fixture.CallKinds());
        Assert.Contains("aligned: covered", File.ReadAllText(
            Path.Combine(fixture.Root, TransactionFixture.BackfillPath)), StringComparison.Ordinal);
        Assert.Empty(fixture.Status());
    }

    private static string Diagnostics(ProcessOutput result) =>
        "stdout:\n" + Encoding.UTF8.GetString(result.StandardOutput)
        + "\nstderr:\n" + Encoding.UTF8.GetString(result.StandardError);

    private sealed partial class TransactionFixture : IDisposable
    {
        internal const string AtomId = "atom-1";
        internal const string Gid = "D5/S0/Carrier/Probe.probe";
        internal const string LeanPath = "D5/S0/Carrier/Probe.lean";
        internal const string DefinitionPath = "Blueprint/D5/S0/Carrier/Probe.scribe.cs";
        internal const string EmissionPath = "Blueprint/D5/S0/Carrier/Probe.md";
        internal const string EchoPath = "Generated/echo-residual-summary.md";
        internal const string LedgerPath = "Meta/StrataLint/Golden/Frozen/accepted";
        internal const string BackfillPath = "Meta/BACKFILL.yaml";
        internal const string ReceiptRelativePath = "Meta/Digestion/formalizations/atom-1.v1.json";

        private const string ScriptPath = "Meta/StrataLint/scripts/workflow/playbook-workflows.sh";
        private readonly TemporaryDirectory temporary = new();
        private readonly string binPath;
        private readonly string callsPath;

        internal TransactionFixture()
        {
            Root = temporary.Path;
            binPath = Path.Combine(Root, "bin");
            callsPath = Path.Combine(Root, "calls");
            Directory.CreateDirectory(binPath);
            CopyScript();
            WriteFile(".gitignore", ".lake/\n.report-source\nbin/\ncalls\nfail-ledger-once\n");
            WriteFile(LeanPath, "theorem probe : True := by trivial\n");
            WriteFile(DefinitionPath, "definition baseline\n");
            WriteFile(EmissionPath, "emission: baseline\n");
            WriteFile(EchoPath, "echo: baseline\n");
            Directory.CreateDirectory(Path.Combine(Root, LedgerPath));
            WriteFile(BackfillPath, $"atom_id: {AtomId}\ncoverage: false\naligned: false\n");
            WriteMakeStub();
            WriteDotnetStub();
            Git("init", "-q");
            Git("config", "user.email", "playbook@example.invalid");
            Git("config", "user.name", "Playbook Test");
            Git("add", "-A");
            Git("commit", "-qm", "fixture baseline");
            File.Copy(Path.Combine(Root, LeanPath), Path.Combine(Root, ".report-source"));
        }

        internal string Root { get; }

        internal string ReceiptPath => Path.Combine(Root, ReceiptRelativePath);

        internal void ChangeFormalization()
        {
            WriteFile(LeanPath, "theorem probe : True := by\n  trivial\n");
            WriteFile(DefinitionPath, "definition deposited\n");
        }

        internal void FailAfterNextFreeze() => WriteFile("fail-ledger-once", "1\n");

        internal void WriteAlignedReceipt() => WriteFile(
            ReceiptRelativePath,
            $"{{\"atom_id\":\"{AtomId}\",\"primary_gid\":\"{Gid}\"}}\n");

        internal void WriteFreezeThenRevoke()
        {
            const string caseId = "active-frozen/revoked-probe";
            const string frozenNodeId =
                "sha256:1111111111111111111111111111111111111111111111111111111111111111";
            var descriptorBlobOid = "git-sha1:" + Git("hash-object", "--", LeanPath).Trim();
            var freeze = JsonSerializer.Serialize(new
            {
                event_type = "Freeze",
                payload = new
                {
                    case_id = caseId,
                    frozen_node_id = frozenNodeId,
                    input = new { descriptor_blob_oid = descriptorBlobOid },
                    node_path = LeanPath,
                },
            });
            var revoke = JsonSerializer.Serialize(new
            {
                event_type = "Revoke",
                payload = new
                {
                    affected_case_ids = new[] { caseId },
                    affected_frozen_node_ids = new[] { frozenNodeId },
                },
            });
            WriteLedger(freeze, revoke);
        }

        internal void WriteActiveFreeze(string descriptorBlobOid)
        {
            var freeze = JsonSerializer.Serialize(new
            {
                event_type = "Freeze",
                payload = new
                {
                    case_id = "active-frozen/stale-probe",
                    frozen_node_id =
                        "sha256:3333333333333333333333333333333333333333333333333333333333333333",
                    input = new { descriptor_blob_oid = descriptorBlobOid },
                    node_path = LeanPath,
                },
            });
            WriteLedger(freeze);
        }

        internal void LeaveInterruptedTemporaryFiles()
        {
            WriteFile(EchoPath + ".tmp.abandoned", "partial echo\n");
            WriteFile(ReceiptRelativePath + ".tmp.abandoned", "partial receipt\n");
        }

        internal ProcessOutput Run(
            string command,
            bool failEcho = false,
            bool staleReport = false,
            bool invalidReceipt = false) =>
            BoundedProcessRunner.Run(
                "/usr/bin/env",
                [
                    $"PATH={binPath}{Path.PathSeparator}{Environment.GetEnvironmentVariable("PATH")}",
                    $"PLAYBOOK_TEST_CALLS={callsPath}",
                    $"PLAYBOOK_FAIL_ECHO={(failEcho ? "1" : "0")}",
                    $"PLAYBOOK_STALE_REPORT={(staleReport ? "1" : "0")}",
                    $"PLAYBOOK_INVALID_RECEIPT={(invalidReceipt ? "1" : "0")}",
                    "/bin/bash",
                    Path.Combine(Root, ScriptPath),
                    command,
                    "synthetic-base",
                    AtomId,
                    Gid,
                ],
                Root,
                TimeSpan.FromSeconds(30),
                128 * 1024);

        internal int CommitCount() => int.Parse(Git("rev-list", "--count", "HEAD").Trim());

        internal int FreezeCount() => Directory.EnumerateFiles(Path.Combine(Root, LedgerPath), "*.json")
            .Count(path =>
            {
                using var document = JsonDocument.Parse(File.ReadAllText(path));
                var root = document.RootElement;
                return root.GetProperty("event_type").GetString() == "Freeze"
                    && root.GetProperty("payload").GetProperty("node_path").GetString() == LeanPath;
            });

        private void WriteLedger(params string[] events)
        {
            var directory = Path.Combine(Root, LedgerPath);
            foreach (var path in Directory.EnumerateFiles(directory, "*.json")) File.Delete(path);
            for (var index = 0; index < events.Length; index++)
            {
                File.WriteAllText(
                    Path.Combine(directory, $"fixture-{index}.json"),
                    events[index] + "\n",
                    new UTF8Encoding(false));
            }
        }

        internal string[] Status() => Git("status", "--porcelain=v1")
            .Split('\n', StringSplitOptions.RemoveEmptyEntries);

        internal string[] CommitPaths(string revision) => Git(
                "show", "--pretty=format:", "--name-only", revision)
            .Split('\n', StringSplitOptions.RemoveEmptyEntries);

        internal string[] TrackedPaths() => Git("ls-files")
            .Split('\n', StringSplitOptions.RemoveEmptyEntries);

        internal string[] CallKinds() => !File.Exists(callsPath)
            ? []
            : File.ReadAllLines(callsPath).Select(static call =>
            {
                if (!call.StartsWith("dotnet:", StringComparison.Ordinal)) return call;
                var command = call["dotnet:".Length..];
                var separator = command.IndexOf(' ');
                return "dotnet:" + (separator < 0 ? command : command[..separator]);
            }).ToArray();

        internal void ClearCalls()
        {
            if (File.Exists(callsPath)) File.Delete(callsPath);
        }

        private void CopyScript()
        {
            var root = FindRepositoryRoot();
            var target = Path.Combine(Root, ScriptPath);
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(Path.Combine(root, ScriptPath), target);
        }

        private string Git(params string[] arguments)
        {
            var result = BoundedProcessRunner.Run(
                "/usr/bin/git",
                arguments,
                Root,
                TimeSpan.FromSeconds(15),
                128 * 1024);
            if (result.ExitCode != 0)
            {
                throw new InvalidOperationException(
                    $"git {string.Join(' ', arguments)} failed: "
                    + Encoding.UTF8.GetString(result.StandardError));
            }

            return Encoding.UTF8.GetString(result.StandardOutput);
        }

        private void WriteExecutable(string name, string body)
        {
            var path = Path.Combine(binPath, name);
            File.WriteAllText(
                path,
                "#!/usr/bin/env bash\nset -euo pipefail\n" + body + "\n",
                new UTF8Encoding(false));
            if (OperatingSystem.IsWindows()) return;
            File.SetUnixFileMode(
                path,
                UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        }

        private void WriteFile(string relativePath, string content)
        {
            var path = Path.Combine(Root, relativePath);
            Directory.CreateDirectory(Path.GetDirectoryName(path) ?? Root);
            File.WriteAllText(path, content, new UTF8Encoding(false));
        }

        public void Dispose() => temporary.Dispose();

        private static string FindRepositoryRoot()
        {
            var directory = new DirectoryInfo(AppContext.BaseDirectory);
            while (directory is not null && !File.Exists(Path.Combine(directory.FullName, "Makefile")))
            {
                directory = directory.Parent;
            }

            return directory?.FullName ?? throw new InvalidOperationException("repository root not found");
        }
    }
}
