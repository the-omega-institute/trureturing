using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DepositCoverWorkflowScriptTests
{
    [Fact]
    public void DepositBuildsEmitsAndFreezesWithoutCommitting()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        var before = fixture.CommitCount();

        var result = fixture.Run("deposit");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Equal(before, fixture.CommitCount());
        Assert.Equal(1, fixture.FreezeCount());
        Assert.Equal(0, fixture.FreezeProbeCount());
        Assert.NotEmpty(fixture.Status());
        Assert.Equal(
            [
                "make:lean-report",
                "dotnet:deposit-header-check",
                "make:emit",
                "dotnet:ledger-append",
            ],
            fixture.CallKinds());
    }

    [Fact]
    public void DepositAfterSnapshotRevocationAppendsANewFreeze()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        fixture.WriteRevokedSnapshot();

        var result = fixture.Run("deposit");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Equal(1, fixture.CallKinds().Count(call => call == "dotnet:ledger-append"));
        Assert.Equal(1, fixture.FreezeCount());
    }

    [Fact]
    public void DepositSkipsFreezeWhenTheModulePathIsAlreadyActive()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        fixture.WriteActiveFreeze();

        var result = fixture.Run("deposit");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.DoesNotContain("dotnet:ledger-append", fixture.CallKinds());
        Assert.Equal(1, fixture.FreezeCount());
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
    public void CoverWritesEdgeAndReemitsWithoutCommitting()
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
        Assert.Equal(before, fixture.CommitCount());
        Assert.Equal(
            [
                "make:lean-report",
                "dotnet:cover-atom",
                "make:emit",
            ],
            fixture.CallKinds());
        Assert.Contains("coverage: true", fixture.BackfillContents(), StringComparison.Ordinal);
        Assert.Equal("emission: covered\n", fixture.EmissionContents());
        Assert.NotEmpty(fixture.Status());
    }

    [Fact]
    public void FailedCoverLeavesDispositionUncommittedBeforeReturningFailure()
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
        Assert.Equal(before, fixture.CommitCount());
        Assert.Contains("cover_disposition:", fixture.BackfillContents(), StringComparison.Ordinal);
        Assert.Equal(["make:lean-report", "dotnet:cover-atom"], fixture.CallKinds());
        Assert.NotEmpty(fixture.Status());
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

        internal void WriteRevokedSnapshot()
        {
            WriteLedger(Array.Empty<string>());
        }

        internal void WriteActiveFreeze()
        {
            var freeze = JsonSerializer.Serialize(new
            {
                event_hash =
                    "sha256:3333333333333333333333333333333333333333333333333333333333333333",
                event_type = "Freeze",
                payload = new
                {
                    declaration_statement_ids = Array.Empty<object>(),
                    descriptor_selector = LeanPath,
                    prerequisite_frozen_node_ids = Array.Empty<string>(),
                    statement_id =
                        "sha256:3333333333333333333333333333333333333333333333333333333333333333",
                },
                schema_version = 5,
            });
            WriteLedger(freeze);
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
                var selector = payload.TryGetProperty(
                    "descriptor_selector",
                    out var descriptorSelector)
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
