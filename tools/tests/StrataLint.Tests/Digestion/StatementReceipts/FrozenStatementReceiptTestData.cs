using System.Collections.Immutable;
using System.Security.Cryptography;
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
        var genesis = FrozenLedgerCanonicalWriter.WriteDagEvent(
            "Genesis",
            JsonSerializer.SerializeToElement(new
            {
                generator_blob_oid = GitOid('a'),
                origin_commit_oid = GitOid('b'),
                origin_tree_oid = GitOid('c'),
                protocol_version = 1,
                rule_catalog_root = Id('d'),
            }));
        AddEvent(files, genesis);

        foreach (var module in modules.OrderBy(static item => item.Path, StringComparer.Ordinal))
        {
            var frozenNodeId = Hash("frozen:" + module.Path);
            var freeze = FrozenLedgerCanonicalWriter.WriteDagEvent(
                "Freeze",
                JsonSerializer.SerializeToElement(new
                {
                    axiom_closure = Array.Empty<string>(),
                    case_id = "active-frozen/" + frozenNodeId["sha256:".Length..],
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
                    frozen_node_id = frozenNodeId,
                    input = new
                    {
                        base_commit_oid = GitOid('b'),
                        base_tree_oid = GitOid('c'),
                        descriptor_blob_oid = GitOid('e'),
                        descriptor_selector = module.Path,
                        supporting_blob_oids = Array.Empty<string>(),
                    },
                    prerequisite_frozen_node_ids = Array.Empty<string>(),
                    statement_id = module.StatementId,
                    witness_id = Hash("witness:" + module.Path),
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

    private static string GitOid(char digit) => "git-sha1:" + new string(digit, 40);

    private static string Hash(string value) =>
        "sha256:" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(value)));
}
