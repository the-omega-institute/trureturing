using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.TestSupport;

internal static class FrozenStatementReceiptTestData
{
    internal sealed record Declaration(
        string Selector,
        string StatementId,
        string? EncodedNameKey = null);

    internal sealed record Module(
        string Path,
        string StatementId,
        ImmutableArray<Declaration> Declarations);

    internal static string Id(char digit) => "sha256:" + new string(digit, 64);

    internal static LeanAxiomReport AddLedger(IDictionary<string, string> files, params Module[] modules)
    {
        var report = Report(modules);
        foreach (var module in modules)
        {
            var inventory = FrozenStateRecord.Project(report.Files[RepoPath.CreateKnown(module.Path)])
                .Where(static declaration => CanonicalLeanNameDecoder.IsRepositoryNameKey(declaration.DeclarationNameKey))
                .ToImmutableArray();
            files[FrozenStatePath.FromModulePath(RepoPath.CreateKnown(module.Path)).Value] =
                Encoding.UTF8.GetString(FrozenStateRecord.Encode(StatementId.Create(module.StatementId), inventory).AsSpan());
        }
        return report;
    }

    internal static LeanAxiomReport Report(params Module[] modules) => LeanAxiomReport.Create(
        modules.ToDictionary(static module => module.Path, static module => new LeanFileReport([], module.Declarations.Select(
            static declaration => new LeanDeclaration(declaration.Selector, "theorem", "True", [])
            { NameKey = declaration.EncodedNameKey ?? NameKey(declaration.Selector), PrecomputedStatementId = declaration.StatementId })
            .ToImmutableArray()), StringComparer.Ordinal));

    internal static (string Path, byte[] Bytes)[] LedgerFiles(out LeanAxiomReport report, params Module[] modules)
    {
        var files = new Dictionary<string, string>(StringComparer.Ordinal);
        report = AddLedger(files, modules);
        return files
            .OrderBy(static item => item.Key, StringComparer.Ordinal)
            .Select(static item => (item.Key, Encoding.UTF8.GetBytes(item.Value)))
            .ToArray();
    }

    internal static string Resolve(IDictionary<string, string> files, string gidText, LeanAxiomReport report)
    {
        var raw = RawRepositorySnapshot.Create(files.Select(static item =>
            RawRepositoryEntry.FromText(item.Key, item.Value)));
        var snapshot = ((SnapshotDecodeOutcome.Decoded)SnapshotDecoder.Decode(raw)).Snapshot;
        if (!Gid.TryParse(gidText, out var gid))
        {
            throw new InvalidOperationException($"invalid fixture GID: {gidText}");
        }

        if (!Index(snapshot, report).TryResolve(
                gid,
                out var statementId,
                out var message))
        {
            throw new InvalidOperationException(message);
        }

        return statementId!.Value;
    }

    internal static FrozenStatementIndex Index(RepositorySnapshot snapshot, LeanAxiomReport report) =>
        FrozenStatementIndex.Create(FrozenStateCatalog.Load(snapshot), report);

    private static string NameKey(string selector)
    {
        var result = "n0";
        foreach (var component in selector.Split('.'))
        {
            result = $"ns({result},{Encoding.UTF8.GetByteCount(component)}:{component})";
        }

        return result;
    }

}
