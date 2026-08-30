using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

// review-envelope --base REV --head REV
//
// 从两棵快照派生合并前评审信封的**分支真值**,不搬任何 worker 散文(#4163;#4117 因手工组装的信封
// 与分支不符损失四轮评审):
//   deposited = head 有而 base 没有的 `Meta/Digestion/formalizations/*.v1.json` 收据(atom_id、primary_gid);
//   ejected   = head 的消化账本里带 receipts.quarantine、而 base 的同一原子没有的条目;
//   fail-closed:head 中任一带 quarantine 的原子同时拥有收据(不限本次新增)→ 由账本 loader 拒绝;零结果 → 拒绝。
// 两个 revision 都由调用方显式给出(第Ⅵ节:判词里的 git 引用只许 head 与 base)。
internal static class ReviewEnvelopeCommand
{
    internal const string Schema = "stratalint-review-envelope-v1";
    internal const string InvalidMarker = "REVIEW_ENVELOPE_INVALID";
    internal const string ConflictMarker = "REVIEW_ENVELOPE_CONFLICT";
    internal const int ConflictExitCode = 3;

    private static readonly JsonSerializerOptions JsonOptions = new()
    {
        WriteIndented = true,
        Encoder = System.Text.Encodings.Web.JavaScriptEncoder.UnsafeRelaxedJsonEscaping,
    };

    internal sealed record Deposited(string AtomId, string Gid, string Receipt);

    internal sealed record Ejected(
        string AtomId,
        string SourceId,
        string BlockerClass,
        string ReentryCondition,
        string Justification);

    // 既有收据在 head 里只许「追加 hosted_extensions」(收据是 SSOT,不重写):其余任何字段改动 → INVALID。
    internal sealed record Extended(string AtomId, string Gid, string Receipt, ImmutableArray<string> AddedGids);

    internal sealed record Derivation(
        ImmutableArray<Deposited> DepositedAtoms,
        ImmutableArray<Ejected> EjectedAtoms,
        ImmutableArray<Extended> ExtendedAtoms);

    internal static CommandResult Run(
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments)
    {
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(arguments);
        try
        {
            var (baseRevision, headRevision) = ParseArguments(arguments);
            var baseSnapshot = Decode(repository.ReadRevision(baseRevision));
            var headSnapshot = Decode(repository.ReadRevision(headRevision));
            var derivation = Derive(baseSnapshot, headSnapshot);
            return new CommandResult(true, Render(baseRevision, headRevision, derivation), string.Empty);
        }
        catch (DigestionQuarantineConflictException conflict)
        {
            // 典型结果:隔离原子同时持有机器形式陈述。由账本 loader 以类型暴露,此处映射为专用退出码 3,
            // 调用方不必解析消息文本(#4163 round 4/5)。
            return new CommandResult(
                false,
                string.Empty,
                $"{ConflictMarker} {conflict.AtomId}: {conflict.Message}\n",
                ExitCode: ConflictExitCode);
        }
        catch (Exception exception) when (
            exception is FormatException
                or JsonException
                or InvalidOperationException
                or IOException
                or ArgumentException)
        {
            return new CommandResult(false, string.Empty, $"{InvalidMarker} {exception.Message}\n");
        }
    }

    // 纯派生:无 git、无进程,测试直接喂两棵合成快照(raw 形式先经 SnapshotDecoder 解码)。
    internal static Derivation Derive(RawRepositorySnapshot baseSnapshot, RawRepositorySnapshot headSnapshot) =>
        Derive(Decode(baseSnapshot), Decode(headSnapshot));

    internal static Derivation Derive(RepositorySnapshot baseSnapshot, RepositorySnapshot headSnapshot)
    {
        ArgumentNullException.ThrowIfNull(baseSnapshot);
        ArgumentNullException.ThrowIfNull(headSnapshot);

        var baseReceipts = ReceiptPaths(baseSnapshot);
        var headReceipts = ReceiptPaths(headSnapshot);
        var baseQuarantined = QuarantinedAtoms(baseSnapshot);
        var headEntries = BackfillInventoryLoader.Load(headSnapshot).RequireDigestionEntries();
        var ledgerByAtom = headEntries.ToImmutableDictionary(static entry => entry.AtomId, StringComparer.Ordinal);

        // 每一份 head 收据都验(不只本次新增的):路径 ↔ atom_id 绑定、账本成员、指纹与 cas_ref 与账本条目一致。
        // 一份被改写过的既有收据同样会让 head 失真;失真的 head 不产信封。
        var validated = headReceipts
            .Order(StringComparer.Ordinal)
            .Select(path =>
            {
                var receipt = DigestionFormalizationReceipt.Load(headSnapshot, path);
                if (DigestionFormalizationReceipt.PathForAtom(receipt.AtomId) != path)
                {
                    throw new FormatException(
                        $"receipt path/atom mismatch: {path} carries atom_id {receipt.AtomId}");
                }
                if (!ledgerByAtom.TryGetValue(receipt.AtomId, out var entry))
                {
                    throw new FormatException(
                        $"receipt for an atom absent from the head ledger: {receipt.AtomId}");
                }
                if (receipt.RawSha256 != entry.Fingerprints.RawSha256 || receipt.CasRef != entry.CasRef)
                {
                    throw new FormatException(
                        $"stale receipt: {receipt.AtomId} fingerprint/cas_ref do not match the head ledger entry");
                }
                return (Path: path, Receipt: receipt);
            })
            .ToImmutableArray();
        var deposited = validated
            .Where(item => !baseReceipts.Contains(item.Path))
            .Select(item => new Deposited(item.Receipt.AtomId, item.Receipt.PrimaryGid, item.Path))
            .ToImmutableArray();
        var extended = validated
            .Where(item => baseReceipts.Contains(item.Path))
            .Select(item => (item.Path, Head: item.Receipt, Base: DigestionFormalizationReceipt.Load(baseSnapshot, item.Path)))
            .Where(static item => !DigestionFormalizationReceipt.Write(item.Base)
                .SequenceEqual(DigestionFormalizationReceipt.Write(item.Head)))
            .Select(static item => ClassifyChangedReceipt(item.Path, item.Base, item.Head))
            .ToImmutableArray();

        var headQuarantined = headEntries
            .Where(static entry => entry.Receipts.Quarantine is not null)
            .ToImmutableArray();
        var ejected = headQuarantined
            .Where(entry => !baseQuarantined.Contains(entry.AtomId))
            .OrderBy(static entry => entry.AtomId, StringComparer.Ordinal)
            .Select(entry => new Ejected(
                entry.AtomId,
                entry.SourceId,
                entry.Receipts.Quarantine!.BlockerClass ?? string.Empty,
                entry.Receipts.Quarantine!.ReentryCondition,
                entry.Receipts.Quarantine!.Justification))
            .ToImmutableArray();

        // HEAD 全域互斥(隔离原子不得同时持有收据,不限本次新增)由 BackfillInventoryLoader.Load 自身
        // fail-closed 执法(「entry X cannot be quarantined because …」),上面的 Load 已经把它抛出;
        // 本命令不再重判一遍(可达性:若这里再写一条检查,它永远不会被执行,变异也不会红)。
        if (deposited.IsEmpty && ejected.IsEmpty && extended.IsEmpty)
        {
            throw new FormatException("no outcome: head adds no receipt, no hosted extension and no quarantine block relative to base");
        }

        return new Derivation(deposited, ejected, extended);
    }

    private static Extended ClassifyChangedReceipt(
        string path,
        DigestionFormalizationReceipt baseReceipt,
        DigestionFormalizationReceipt headReceipt)
    {
        var baseExtensions = baseReceipt.HostedExtensions.IsDefault ? [] : baseReceipt.HostedExtensions;
        var headExtensions = headReceipt.HostedExtensions.IsDefault ? [] : headReceipt.HostedExtensions;
        var rootUnchanged = baseReceipt.AtomId == headReceipt.AtomId
            && baseReceipt.PrimaryGid == headReceipt.PrimaryGid
            && baseReceipt.Signature == headReceipt.Signature
            && baseReceipt.CasRef == headReceipt.CasRef
            && baseReceipt.RawSha256 == headReceipt.RawSha256;
        var baseKept = baseExtensions.All(extension => headExtensions.Contains(extension));
        var added = headExtensions
            .Where(extension => !baseExtensions.Contains(extension))
            .Select(static extension => extension.Gid)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        if (!rootUnchanged || !baseKept || added.IsEmpty)
        {
            throw new FormatException(
                $"rewritten receipt: {path} — an existing receipt may only gain hosted_extensions (root fields and prior extensions must be unchanged)");
        }
        return new Extended(headReceipt.AtomId, headReceipt.PrimaryGid, path, added);
    }

    private static ImmutableHashSet<string> ReceiptPaths(RepositorySnapshot snapshot) =>
        snapshot.Files.Keys
            .Select(static key => key.Value)
            .Where(static path => path.StartsWith(DigestionFormalizationReceipt.RootPath, StringComparison.Ordinal)
                && path.EndsWith(DigestionFormalizationReceipt.PathSuffix, StringComparison.Ordinal))
            .ToImmutableHashSet(StringComparer.Ordinal);

    private static ImmutableHashSet<string> QuarantinedAtoms(RepositorySnapshot snapshot) =>
        BackfillInventoryLoader.Load(snapshot).RequireDigestionEntries()
            .Where(static entry => entry.Receipts.Quarantine is not null)
            .Select(static entry => entry.AtomId)
            .ToImmutableHashSet(StringComparer.Ordinal);

    private static (string Base, string Head) ParseArguments(IReadOnlyList<string> arguments)
    {
        string? baseRevision = null;
        string? headRevision = null;
        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--base" when index + 1 < arguments.Count && baseRevision is null:
                    baseRevision = arguments[++index];
                    break;
                case "--head" when index + 1 < arguments.Count && headRevision is null:
                    headRevision = arguments[++index];
                    break;
                default:
                    throw new ArgumentException("usage: review-envelope --base REV --head REV");
            }
        }
        if (string.IsNullOrWhiteSpace(baseRevision) || string.IsNullOrWhiteSpace(headRevision))
        {
            throw new ArgumentException("usage: review-envelope --base REV --head REV");
        }
        return (baseRevision, headRevision);
    }

    private static string Render(string baseRevision, string headRevision, Derivation derivation)
    {
        var material = new
        {
            schema = Schema,
            @base = baseRevision,
            head = headRevision,
            deposited = derivation.DepositedAtoms.Select(static atom => new
            {
                atom_id = atom.AtomId,
                gid = atom.Gid,
                receipt = atom.Receipt,
            }).ToArray(),
            ejected = derivation.EjectedAtoms.Select(static atom => new
            {
                atom_id = atom.AtomId,
                source_id = atom.SourceId,
                blocker_class = atom.BlockerClass,
                reentry_condition = atom.ReentryCondition,
                justification = atom.Justification,
            }).ToArray(),
            extended = derivation.ExtendedAtoms.Select(static atom => new
            {
                atom_id = atom.AtomId,
                gid = atom.Gid,
                receipt = atom.Receipt,
                added_gids = atom.AddedGids.ToArray(),
            }).ToArray(),
        };
        return JsonSerializer.Serialize(material, JsonOptions) + "\n";
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };
}
