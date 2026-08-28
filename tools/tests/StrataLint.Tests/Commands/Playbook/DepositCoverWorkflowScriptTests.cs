using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DepositCoverWorkflowScriptTests
{
    [Fact]
    public void DepositWithExactSixLineHeaderRunsPhaseAEmissionWithoutRecomputingAfterFreezeAndReceipt()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        var before = fixture.CommitCount();

        var result = fixture.Run("deposit");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Equal(before + 2, fixture.CommitCount());
        Assert.Equal(1, fixture.FreezeCount());
        Assert.Equal(0, fixture.FreezeProbeCount());
        Assert.True(File.Exists(fixture.ReceiptPath));
        Assert.Empty(fixture.Status());
        Assert.Equal(
            [
                "make:lean-report",
                "dotnet:deposit-header-check",
                "make:emit",
                "dotnet:emit-formalization-receipt",
                "dotnet:ledger-append",
            ],
            fixture.CallKinds());

        var phaseA = fixture.CommitPaths("HEAD~1");
        Assert.Contains(TransactionFixture.LeanPath, phaseA);
        Assert.Contains(TransactionFixture.DefinitionPath, phaseA);
        Assert.Contains(TransactionFixture.EmissionPath, phaseA);
        Assert.DoesNotContain(TransactionFixture.LedgerPath, phaseA);
        Assert.DoesNotContain(TransactionFixture.ReceiptRelativePath, phaseA);

        var phaseB = fixture.CommitPaths("HEAD");
        Assert.Contains(
            phaseB,
            path => path.StartsWith(TransactionFixture.LedgerPath + "/", StringComparison.Ordinal));
        Assert.Contains(TransactionFixture.ReceiptRelativePath, phaseB);
    }

    [Fact]
    public void DepositReentryWithExistingFreezeAndMissingReceiptRecoversWithoutLeanReport()
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
        fixture.ClearCalls();

        var resumed = fixture.Run("deposit");

        Assert.True(resumed.ExitCode == 0, Diagnostics(resumed));
        Assert.Equal(before + 2, fixture.CommitCount());
        Assert.Equal(1, fixture.FreezeCount());
        Assert.DoesNotContain("dotnet:ledger-append", fixture.CallKinds());
        Assert.Equal(
            ["dotnet:deposit-header-check", "dotnet:emit-formalization-receipt"],
            fixture.CallKinds());
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
        fixture.ClearCalls();

        var resumed = fixture.Run("deposit");

        Assert.True(resumed.ExitCode == 0, Diagnostics(resumed));
        Assert.Equal(before + 2, fixture.CommitCount());
        Assert.Equal(1, fixture.FreezeCount());
        Assert.DoesNotContain("dotnet:ledger-append", fixture.CallKinds());
        Assert.Equal(
            ["dotnet:deposit-header-check", "dotnet:emit-formalization-receipt"],
            fixture.CallKinds());
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
    public void DepositSkipsFreezeWhenTheModulePathIsAlreadyActive()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        fixture.WriteActiveFreeze(
            "git-sha1:0000000000000000000000000000000000000000");

        var result = fixture.Run("deposit");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.DoesNotContain("dotnet:ledger-append", fixture.CallKinds());
        Assert.Equal(1, fixture.FreezeCount());
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
    public void DepositFailsClosedWhenLeanReportRemainsStale()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();

        var result = fixture.Run("deposit", staleReport: true);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("STALE_LEAN_REPORT", Encoding.UTF8.GetString(result.StandardError), StringComparison.Ordinal);
        Assert.Equal(
            ["make:lean-report", "dotnet:deposit-header-check", "make:emit"],
            fixture.CallKinds());
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
    public void DepositRejectsInvalidExistingHostReceiptBeforeAppendingSecondaryFreeze()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        var primary = fixture.Run("deposit");
        Assert.True(primary.ExitCode == 0, Diagnostics(primary));
        fixture.WriteHostReceipt(atomId: "wrong-atom");
        fixture.AddSecondaryFormalization();

        var secondary = fixture.Run("deposit", TransactionFixture.SecondaryGid);

        Assert.NotEqual(0, secondary.ExitCode);
        Assert.Contains(
            "existing formalization receipt conflicts",
            Encoding.UTF8.GetString(secondary.StandardError),
            StringComparison.Ordinal);
        Assert.Equal(1, fixture.FreezeCount(TransactionFixture.LeanPath));
        Assert.Equal(0, fixture.FreezeCount(TransactionFixture.SecondaryLeanPath));
    }

    [Fact]
    public void DepositFreezesASecondModuleUnderTheExistingAtomReceiptHost()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        var primary = fixture.Run("deposit");
        Assert.True(primary.ExitCode == 0, Diagnostics(primary));
        var receipt = File.ReadAllBytes(fixture.ReceiptPath);
        fixture.AddSecondaryFormalization();
        fixture.ClearCalls();

        var secondary = fixture.Run("deposit", TransactionFixture.SecondaryGid);

        Assert.True(secondary.ExitCode == 0, Diagnostics(secondary));
        Assert.Contains(fixture.Calls(), call => call.StartsWith(
            "dotnet:emit-formalization-receipt"
                + $" --atom-id {TransactionFixture.AtomId}"
                + $" --gid {TransactionFixture.SecondaryGid}",
            StringComparison.Ordinal));
        Assert.DoesNotContain(fixture.Calls(), call =>
            call.Contains("--require-existing-coverage", StringComparison.Ordinal));
        Assert.Equal(1, fixture.FreezeCount(TransactionFixture.LeanPath));
        Assert.Equal(1, fixture.FreezeCount(TransactionFixture.SecondaryLeanPath));
        Assert.NotEqual(receipt, File.ReadAllBytes(fixture.ReceiptPath));
        using var document = JsonDocument.Parse(File.ReadAllBytes(fixture.ReceiptPath));
        Assert.Equal(TransactionFixture.Gid,
            document.RootElement.GetProperty("primary_gid").GetString());
        var extension = Assert.Single(
            document.RootElement.GetProperty("hosted_extensions").EnumerateArray());
        Assert.Equal(TransactionFixture.SecondaryGid, extension.GetProperty("gid").GetString());
        var signature = extension.GetProperty("precommitted_signature");
        Assert.Equal("window_register_crt_decomposition",
            signature.GetProperty("name_key").GetString());
        Assert.Equal("theorem", signature.GetProperty("kind").GetString());
        Assert.Equal("True", signature.GetProperty("type").GetString());
        Assert.Single(Directory.EnumerateFiles(
            Path.GetDirectoryName(fixture.ReceiptPath)!, "*.v1.json"));
        Assert.Empty(fixture.Status());
    }

    [Fact]
    public void DepositRejectsAHostReceiptChangedAfterExtensionValidation()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        var primary = fixture.Run("deposit");
        Assert.True(primary.ExitCode == 0, Diagnostics(primary));
        fixture.AddSecondaryFormalization();
        var concurrentReceipt =
            $"{{\"atom_id\":\"{TransactionFixture.AtomId}\","
            + $"\"primary_gid\":\"{TransactionFixture.Gid}\",\"concurrent\":true}}\n";

        var secondary = fixture.Run(
            "deposit",
            TransactionFixture.SecondaryGid,
            mutateReceiptAfterPrepare: concurrentReceipt);

        Assert.NotEqual(0, secondary.ExitCode);
        Assert.Contains(
            "changed after extension validation",
            Encoding.UTF8.GetString(secondary.StandardError),
            StringComparison.Ordinal);
        Assert.Equal(concurrentReceipt, File.ReadAllText(fixture.ReceiptPath));
    }

    [Fact]
    public void DepositAndCoverHostArchivedWindowRegisterCrtUnderTheExistingAtomReceipt()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        var primaryDeposit = fixture.Run("deposit");
        Assert.True(primaryDeposit.ExitCode == 0, Diagnostics(primaryDeposit));
        var primaryCover = fixture.Run("cover");
        Assert.True(primaryCover.ExitCode == 0, Diagnostics(primaryCover));
        fixture.AddSecondaryFormalization();
        var deposit = fixture.Run("deposit", TransactionFixture.SecondaryGid);
        Assert.True(deposit.ExitCode == 0, Diagnostics(deposit));
        fixture.ClearCalls();

        var cover = fixture.Run("cover", TransactionFixture.SecondaryGid);

        Assert.True(cover.ExitCode == 0, Diagnostics(cover));
        Assert.Contains(
            "dotnet:cover-atom --cover-atom atom-1"
                + $" --gid {TransactionFixture.SecondaryGid}"
                + " --base synthetic-base"
                + $" --envelope {TransactionFixture.ReceiptRelativePath}",
            fixture.Calls());
        Assert.Empty(fixture.Status());
    }

    [Fact]
    public void CoverAlignsThenReemitsAndCommitsOnce()
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
                "dotnet:align-scribe-receipt",
                "make:emit",
            ],
            fixture.CallKinds());
        Assert.Contains("aligned: covered", fixture.BackfillContents(), StringComparison.Ordinal);
        Assert.Equal("emission: covered\n", fixture.EmissionContents());
        Assert.Empty(fixture.Status());
    }

    [Fact]
    public void FailedCoverCommitsDispositionBeforeReturningFailure()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        var before = fixture.CommitCount();

        var result = fixture.Run("cover", coverDispositionFailure: true);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(
            "COVER_INVALID synthetic disposition",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
        Assert.Equal(before + 1, fixture.CommitCount());
        Assert.Contains("cover_disposition:", fixture.BackfillContents(), StringComparison.Ordinal);
        Assert.Equal(["make:lean-report", "dotnet:cover-atom"], fixture.CallKinds());
        Assert.Empty(fixture.Status());
    }

    private static string Diagnostics(ProcessOutput result) =>
        "stdout:\n" + Encoding.UTF8.GetString(result.StandardOutput)
        + "\nstderr:\n" + Encoding.UTF8.GetString(result.StandardError);

    internal sealed partial class TransactionFixture : IDisposable
    {
        internal const string AtomId = "atom-1";
        internal const string SecondaryAtomId = "atom-2";
        internal const string Gid = "D5/S0/Carrier/Probe.probe";
        internal const string LeanPath = "D5/S0/Carrier/Probe.lean";
        internal const string SecondaryGid =
            "D5/S3/Observer/WindowRegisterCRT.window_register_crt_decomposition";
        internal const string SecondaryLeanPath = "D5/S3/Observer/WindowRegisterCRT.lean";
        internal const string NewGid = "D5/S2/NewModule.new_module";
        internal const string NewLeanPath = "D5/S2/NewModule.lean";
        internal const string NewEmissionPath = "Blueprint/D5/S2/NewModule.md";
        internal const string DefinitionPath = "Blueprint/D5/S0/Carrier/Probe.scribe.cs";
        internal const string EmissionPath = "Blueprint/D5/S0/Carrier/Probe.md";
        internal const string LedgerPath = FrozenLedgerChangeClassifier.AcceptedRoot;
        internal const string BackfillPath = "Meta/BACKFILL.yaml";
        internal const string ReceiptRelativePath = "Meta/Digestion/formalizations/atom-1.v1.json";
        internal const string SecondaryReceiptRelativePath =
            "Meta/Digestion/formalizations/atom-2.v1.json";

        private const string ScriptPath = "tools/scripts/workflow/playbook-workflows.sh";
        private readonly TemporaryDirectory temporary = new();
        private readonly string binPath;
        private readonly string callsPath;
        private readonly string freezeProbePath;

        internal TransactionFixture()
        {
            Root = temporary.Path;
            binPath = Path.Combine(Root, "bin");
            callsPath = Path.Combine(Root, "calls");
            freezeProbePath = Path.Combine(Root, "freeze-probes");
            Directory.CreateDirectory(binPath);
            CopyScript();
            File.Copy(
                Path.Combine(TestRepositoryLayout.FindRoot(), "Makefile"),
                Path.Combine(Root, "Makefile"));
            WriteFile(
                ".gitignore",
                ".lake/\n.report-source\nbin/\ncalls\nfreeze-probes\nfail-ledger-once\n");
            WriteFile(LeanPath, ExactSixLineLean(Gid, "theorem probe : True := by trivial\n"));
            WriteFile(DefinitionPath, "definition baseline\n");
            WriteFile(EmissionPath, "emission: baseline\n");
            Directory.CreateDirectory(Path.Combine(Root, LedgerPath));
            File.WriteAllBytes(Path.Combine(binPath, "StrataLint.Cli.dll"), []);
            WriteFile(BackfillPath, $"atom_id: {AtomId}\ncoverage: false\naligned: false\n");
            WriteMakeStub();
            WriteDotnetStub();
            WriteGitGuardStub();
            Git("init", "-q");
            Git("config", "user.email", "playbook@example.invalid");
            Git("config", "user.name", "Playbook Test");
            Git("add", "-A");
            Git("commit", "-qm", "fixture baseline");
            File.Copy(Path.Combine(Root, LeanPath), Path.Combine(Root, ".report-source"));
        }

        internal string Root { get; }

        internal string ReceiptPath => Path.Combine(Root, ReceiptRelativePath);

        internal string BackfillContents() => File.ReadAllText(Path.Combine(Root, BackfillPath));

        internal string EmissionContents() => File.ReadAllText(Path.Combine(Root, EmissionPath));

        internal void ChangeFormalization()
        {
            WriteFile(LeanPath, ExactSixLineLean(Gid, "theorem probe : True := by\n  trivial\n"));
            WriteFile(DefinitionPath, "definition deposited\n");
        }

        internal void AddNewFormalization(bool withMirror)
        {
            WriteFile(NewLeanPath, ExactSixLineLean(NewGid, "theorem new_module : True := by trivial\n"));
            if (withMirror)
            {
                WriteFile(NewEmissionPath, "emission: new module\n");
            }
        }

        internal void AddSecondaryFormalization()
        {
            WriteFile(SecondaryLeanPath,
                ExactSixLineLean(
                    SecondaryGid,
                    "theorem window_register_crt_decomposition : True := by trivial\n"));
            WriteFile(
                "Blueprint/D5/S3/Observer/WindowRegisterCRT.scribe.cs",
                "secondary definition\n");
            WriteFile(
                "Blueprint/D5/S3/Observer/WindowRegisterCRT.md",
                "secondary emission\n");
        }

        internal void FailAfterNextFreeze() => WriteFile("fail-ledger-once", "1\n");

        internal void WriteAlignedReceipt() => WriteFile(
            ReceiptRelativePath,
            $"{{\"atom_id\":\"{AtomId}\",\"primary_gid\":\"{Gid}\"}}\n");

        internal void WriteHostReceipt(string atomId = AtomId, string primaryGid = Gid) => WriteFile(
            ReceiptRelativePath,
            $"{{\"atom_id\":\"{atomId}\",\"primary_gid\":\"{primaryGid}\"}}\n");

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
                    input = new
                    {
                        descriptor_blob_oid = descriptorBlobOid,
                        descriptor_selector = LeanPath,
                    },
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
                    input = new
                    {
                        descriptor_blob_oid = descriptorBlobOid,
                        descriptor_selector = LeanPath,
                    },
                    node_path = LeanPath,
                },
            });
            WriteLedger(freeze);
        }

        internal void LeaveInterruptedTemporaryFiles(
            string receiptRelativePath = ReceiptRelativePath)
        {
            WriteFile(receiptRelativePath + ".tmp.abandoned", "partial receipt\n");
        }

        internal int CommitCount() => int.Parse(Git("rev-list", "--count", "HEAD").Trim());

        internal int FreezeCount(string leanPath = LeanPath) =>
            Directory.EnumerateFiles(Path.Combine(Root, LedgerPath), "*.json")
            .Count(path =>
            {
                using var document = JsonDocument.Parse(File.ReadAllText(path));
                var root = document.RootElement;
                if (!root.TryGetProperty("event_type", out var eventType)
                    || eventType.GetString() != "Freeze")
                {
                    return false;
                }

                var payload = root.GetProperty("payload");
                var selector = payload.TryGetProperty("input", out var input)
                    && input.TryGetProperty("descriptor_selector", out var descriptorSelector)
                        ? descriptorSelector.GetString()
                        : null;
                return selector == leanPath;
            });

        private void WriteLedger(params string[] events)
        {
            WriteLedger(events.Select(static (json, index) => ($"fixture-{index}.json", json)).ToArray());
        }

        private void WriteLedger(params (string FileName, string Json)[] events)
        {
            var directory = Path.Combine(Root, LedgerPath);
            foreach (var path in Directory.EnumerateFiles(directory, "*.json")) File.Delete(path);
            foreach (var (fileName, json) in events)
            {
                File.WriteAllText(
                    Path.Combine(directory, fileName),
                    json + "\n",
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

        internal string[] LedgerState() =>
            Directory.EnumerateFiles(Path.Combine(Root, LedgerPath), "*.json")
                .Order(StringComparer.Ordinal)
                .Select(path => Path.GetRelativePath(Root, path) + "\n" + File.ReadAllText(path))
                .ToArray();

        internal string[] CallKinds() => !File.Exists(callsPath)
            ? []
            : File.ReadAllLines(callsPath).Select(static call =>
            {
                if (!call.StartsWith("dotnet:", StringComparison.Ordinal)) return call;
                var command = call["dotnet:".Length..];
                var separator = command.IndexOf(' ');
                return "dotnet:" + (separator < 0 ? command : command[..separator]);
            }).ToArray();

        internal string[] Calls() => File.Exists(callsPath) ? File.ReadAllLines(callsPath) : [];

        internal void ClearCalls()
        {
            if (File.Exists(callsPath)) File.Delete(callsPath);
        }

        private string Git(params string[] arguments)
        {
            var result = TestProcessRunner.Run(
                "/usr/bin/git",
                arguments,
                Root,
                TestBudgets.PlaybookProcessHangGuard,
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

    }
}
