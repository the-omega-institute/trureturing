using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

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

    internal static void AddLedger(
        IDictionary<string, string> files,
        params Module[] modules)
    {
        foreach (var module in modules.OrderBy(static item => item.Path, StringComparer.Ordinal))
        {
            var freeze = FrozenLedgerCanonicalWriter.WriteDagEvent(
                "Freeze",
                JsonSerializer.SerializeToElement(new
                {
                    declaration_statement_ids = module.Declarations
                        .OrderBy(
                            static declaration => declaration.EncodedNameKey
                                ?? NameKey(declaration.Selector),
                            StringComparer.Ordinal)
                        .Select(static declaration => new
                        {
                            declaration_name_key = declaration.EncodedNameKey
                                ?? NameKey(declaration.Selector),
                            kind = "theorem",
                            statement_id = declaration.StatementId,
                        }),
                    descriptor_selector = module.Path,
                    prerequisite_frozen_node_ids = Array.Empty<string>(),
                    statement_id = module.StatementId,
                }));
            AddEvent(files, freeze);
        }
    }

    internal static (string Path, byte[] Bytes)[] LedgerFiles(params Module[] modules)
    {
        var files = new Dictionary<string, string>(StringComparer.Ordinal);
        AddLedger(files, modules);
        return files
            .OrderBy(static item => item.Key, StringComparer.Ordinal)
            .Select(static item => (item.Key, Encoding.UTF8.GetBytes(item.Value)))
            .ToArray();
    }

    internal static string Resolve(IDictionary<string, string> files, string gidText)
    {
        var raw = RawRepositorySnapshot.Create(files.Select(static item =>
            RawRepositoryEntry.FromText(item.Key, item.Value)));
        var snapshot = ((SnapshotDecodeOutcome.Decoded)SnapshotDecoder.Decode(raw)).Snapshot;
        if (!Gid.TryParse(gidText, out var gid))
        {
            throw new InvalidOperationException($"invalid fixture GID: {gidText}");
        }

        if (!FrozenStatementIndex.Load(snapshot).TryResolve(
                gid,
                out var statementId,
                out var message))
        {
            throw new InvalidOperationException(message);
        }

        return statementId!.Value;
    }

    private static void AddEvent(
        IDictionary<string, string> files,
        (ImmutableArray<byte> Bytes, string Hash) encoded) =>
        files[$"{FrozenLedgerChangeClassifier.AcceptedRoot}/{encoded.Hash["sha256:".Length..]}.json"] =
            Encoding.UTF8.GetString(encoded.Bytes.AsSpan());

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
