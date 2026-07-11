using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text.Json;

namespace StrataLint.Engine;

public static class FrozenLedgerMaterializer
{
    public static FrozenMaterialOutcome Build(
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean,
        AcyclicTruthDag dag,
        FrozenLedgerSyntax syntax)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(lean);
        ArgumentNullException.ThrowIfNull(dag);
        ArgumentNullException.ThrowIfNull(syntax);
        try
        {
            if (syntax.Lines.Length == 0)
            {
                throw new FormatException("Frozen ledger is empty.");
            }

            var genesis = syntax.Lines[0].Value.GetProperty("payload");
            var originCommit = RequiredString(genesis, "origin_commit_oid");
            var originTree = RequiredString(genesis, "origin_tree_oid");
            if (!snapshot.TryGetFile("lean-toolchain", out var toolchain)
                || !snapshot.TryGetFile("lake-manifest.json", out var manifest))
            {
                throw new FormatException("Frozen environment source files are missing.");
            }

            var algorithm = originCommit.StartsWith("git-sha256:", StringComparison.Ordinal)
                ? HashAlgorithmName.SHA256
                : HashAlgorithmName.SHA1;
            var environment = new FrozenEnvironmentAttestation(
                originCommit,
                originTree,
                FrozenContentAddress.ComputeGitBlobOid(toolchain.RawBytes.AsSpan(), algorithm),
                FrozenContentAddress.ComputeGitBlobOid(manifest.RawBytes.AsSpan(), algorithm));
            var inputs = new Dictionary<RepoPath, FrozenLedgerInput>();
            var pathsByCase = new Dictionary<string, RepoPath>(StringComparer.Ordinal);
            foreach (var line in syntax.Lines)
            {
                var root = line.Value;
                if (root.ValueKind != JsonValueKind.Object
                    || !root.TryGetProperty("event_type", out var eventType)
                    || eventType.ValueKind != JsonValueKind.String
                    || !root.TryGetProperty("payload", out var payload)
                    || payload.ValueKind != JsonValueKind.Object)
                {
                    continue;
                }

                if (eventType.GetString() == "Freeze")
                {
                    var pathText = RequiredString(payload, "node_path");
                    if (!RepoPath.TryCreate(pathText, out var path))
                    {
                        throw new FormatException($"Freeze has invalid node_path {pathText}.");
                    }

                    var input = ParseMaterialInput(payload.GetProperty("input"));
                    inputs[path] = input;
                    pathsByCase[RequiredString(payload, "case_id")] = path;
                }
                else if (eventType.GetString() == "Reattest")
                {
                    var caseId = RequiredString(payload, "case_id");
                    if (!pathsByCase.TryGetValue(caseId, out var path))
                    {
                        throw new FormatException("Reattest refers to a case not introduced by a prior Freeze.");
                    }

                    inputs[path] = ParseMaterialInput(payload.GetProperty("input"));
                }
            }

            var attestations = dag.Nodes
                .Where(static node => node.State is TruthState.Closed && node.ModuleName is not null)
                .Select(node => inputs.TryGetValue(node.RepoPath, out var input)
                    ? new FrozenModuleAttestation(node.RepoPath, input.DescriptorBlobOid)
                    {
                        BaseCommitOid = input.BaseCommitOid,
                        BaseTreeOid = input.BaseTreeOid,
                    }
                    : throw new FormatException(
                        $"Closed module {node.RepoPath.Value} has no Freeze attestation."))
                .ToImmutableArray();
            return FrozenContentAddress.Build(snapshot, lean, dag, environment, attestations);
        }
        catch (Exception exception) when (
            exception is FormatException or InvalidOperationException or JsonException or KeyNotFoundException)
        {
            return new FrozenMaterialOutcome.Rejected(exception.Message);
        }
    }

    private static string RequiredString(JsonElement value, string name) =>
        value.TryGetProperty(name, out var property) && property.ValueKind == JsonValueKind.String
            ? property.GetString() ?? throw new FormatException($"{name} must not be null.")
            : throw new FormatException($"{name} must be a string.");

    private static FrozenLedgerInput ParseMaterialInput(JsonElement value)
    {
        if (value.ValueKind != JsonValueKind.Object)
        {
            throw new FormatException("Freeze/Reattest input must be an object.");
        }

        var supporting = value.GetProperty("supporting_blob_oids");
        if (supporting.ValueKind != JsonValueKind.Array)
        {
            throw new FormatException("supporting_blob_oids must be an array.");
        }

        return new FrozenLedgerInput(
            RequiredString(value, "base_commit_oid"),
            RequiredString(value, "base_tree_oid"),
            RequiredString(value, "descriptor_blob_oid"),
            RequiredString(value, "descriptor_selector"),
            RequiredString(value, "materializer"),
            supporting.EnumerateArray()
                .Select(static item => item.ValueKind == JsonValueKind.String
                    ? item.GetString() ?? throw new FormatException("supporting blob OID is null.")
                    : throw new FormatException("supporting blob OID must be a string."))
                .ToImmutableArray());
    }
}
