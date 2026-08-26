using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal static class FrozenStatementReceiptTestData
{
    internal sealed record Declaration(string Selector, string StatementId);

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
                    case_id = "active-frozen/" + frozenNodeId["sha256:".Length..],
                    declaration_statement_ids = module.Declarations
                        .OrderBy(static declaration => declaration.Selector, StringComparer.Ordinal)
                        .Select(static declaration => new
                        {
                            declaration_name_key = NameKey(declaration.Selector),
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
                    axiom_closure = Array.Empty<string>(),
                }));
            AddEvent(files, freeze);
        }
    }

    private static void AddEvent(
        IDictionary<string, string> files,
        (ImmutableArray<byte> Bytes, string Hash) encoded) =>
        files[$"{FrozenLedgerChangeClassifier.AcceptedRoot}/{encoded.Hash["sha256:".Length..]}.json"] =
            Encoding.UTF8.GetString(encoded.Bytes.AsSpan());

    private static string NameKey(string selector) =>
        $"ns(n0,{Encoding.UTF8.GetByteCount(selector)}:{selector})";

    private static string GitOid(char digit) => "git-sha1:" + new string(digit, 40);

    private static string Hash(string value) =>
        "sha256:" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(value)));
}
