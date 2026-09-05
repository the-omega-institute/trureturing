using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

// 两个 CLI 测试替身:StubCliEnvironment(9 个测试文件消费)与
// BufferedConsole(17 个)。它们此前住在 CliOutcomeTests.cs —— 一个以某测试类
// 命名的文件里,而消费面比那个测试类大得多,按文件名找不到。
// 纯搬迁:类型、可见性、成员逐字不变;本文件不含测试方法。

internal sealed class StubCliEnvironment(
    AdmissionOutcome outcome,
    ExplicitCommandResult? echoVerify = null,
    ExplicitCommandResult? fileMapConform = null,
    CommandResult? cleanLanes = null,
    ExplicitCommandResult? capacityAudit = null,
    Func<IReadOnlyList<string>, CommandResult>? alignLedger = null) : ICliEnvironment
{
    internal IReadOnlyList<string> CleanLanesArguments { get; private set; } = [];

    public AdmissionOutcome Check(IReadOnlyList<string> arguments) => outcome;

    public ExplicitCommandResult CapacityAudit(IReadOnlyList<string> arguments) =>
        capacityAudit ?? new(2, string.Empty, "capacity audit is not configured in this fixture");

    public AdmissionTopologyOutcome Topology(IReadOnlyList<string> arguments) =>
        new AdmissionTopologyOutcome.InfrastructureFailure("topology is not configured in this fixture");

    public CommandResult Coverage(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "coverage is not configured in this fixture");

    public CommandResult DigestStatus(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "digest status is not configured in this fixture");

    public CommandResult ShowAtom(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "show atom is not configured in this fixture");

    public ExplicitCommandResult EchoVerify(IReadOnlyList<string> arguments) =>
        echoVerify ?? new(2, string.Empty, "echo verify is not configured in this fixture");

    public ExplicitCommandResult GateAuthority(IReadOnlyList<string> arguments) =>
        new(2, string.Empty, "gate authority is not configured in this fixture");

    public ExplicitCommandResult FileMapConform(IReadOnlyList<string> arguments) =>
        fileMapConform ?? new(2, string.Empty, "filemap conformance is not configured in this fixture");

    public ExplicitCommandResult DepositHeaderCheck(IReadOnlyList<string> arguments) =>
        new(2, string.Empty, "deposit header check is not configured in this fixture");

    public ExplicitCommandResult LedgerFrozen(IReadOnlyList<string> arguments) =>
        new(2, string.Empty, "ledger frozen is not configured in this fixture");

    public CommandResult Ingest(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "ingest is not configured in this fixture");

    public CommandResult AlignDigestionStatus(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "align digestion status is not configured in this fixture");

    public CommandResult CoverAtom(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "cover-atom is not configured in this fixture");

    public CommandResult AlignScribeReceipt(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "align-scribe-receipt is not configured in this fixture");

    public CommandResult Route(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "route is not configured in this fixture");

    public CommandResult SelfTest(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "selftest is not configured in this fixture");

    public CommandResult RenderDag(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "dag rendering is not configured in this fixture");

    public CommandResult AlignLedger(IReadOnlyList<string> arguments) =>
        alignLedger?.Invoke(arguments)
            ?? new(false, string.Empty, "ledger align is not configured in this fixture");

    public CommandResult AppendLedger(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "ledger append is not configured in this fixture");

    public CommandResult RevokeLedger(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "ledger revoke is not configured in this fixture");

    public CommandResult ReanchorMathlibLedger(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "mathlib ledger reanchor is not configured in this fixture");

    public ExplicitCommandResult TruthExport(IReadOnlyList<string> arguments) =>
        new(2, string.Empty, "truth export is not configured in this fixture");

    public ExplicitCommandResult TruthRelease(IReadOnlyList<string> arguments) =>
        new(2, string.Empty, "truth release is not configured in this fixture");

    public CommandResult CleanLanes(IReadOnlyList<string> arguments)
    {
        CleanLanesArguments = arguments.ToArray();
        return cleanLanes ?? new(false, string.Empty, "clean lanes is not configured in this fixture");
    }

    public CommandResult Worktree(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "worktree is not configured in this fixture");
}

internal sealed class BufferedConsole : ICliConsole
{
    private readonly StringBuilder output = new();
    private readonly StringBuilder error = new();

    internal string Output => output.ToString();

    internal string Error => error.ToString();

    public void WriteOutput(string value) => output.Append(value);

    public void WriteError(string value) => error.Append(value);
}
