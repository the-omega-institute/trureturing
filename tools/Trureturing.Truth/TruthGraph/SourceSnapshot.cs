using System.Collections.Immutable;
using System.Text;
using System.Text.Json;

namespace Trureturing.Truth;

/// <summary>The exact typed contents of a <c>source-snapshot.v1.json</c> release artifact.</summary>
public sealed record SourceSnapshotModel(
    string Schema,
    string SourceRepo,
    string SourceCommit,
    string SourceTree,
    string LeanToolchain,
    string MathlibRev,
    string ProducerPackageCommit,
    string TruthGraphSha256,
    string RawLeanReportSha256,
    string DagMdSha256,
    string ResidualFrontierSha256,
    string DeclarationsSha256,
    string FrozenLedgerHeadHash,
    int FrozenLedgerSequence);

/// <summary>
/// Canonical writer for <c>source-snapshot.v1.json</c>. The reader remains the schema authority: every
/// emitted model is read back before its bytes are returned, so the owned read and write shapes cannot
/// silently diverge.
/// </summary>
public static class SourceSnapshotJsonWriter
{
    public static ImmutableArray<byte> Write(SourceSnapshotModel model)
    {
        ArgumentNullException.ThrowIfNull(model);
        var element = JsonSerializer.SerializeToElement(new
        {
            schema = model.Schema,
            source_repo = model.SourceRepo,
            source_commit = model.SourceCommit,
            source_tree = model.SourceTree,
            lean_toolchain = model.LeanToolchain,
            mathlib_rev = model.MathlibRev,
            producer_package_commit = model.ProducerPackageCommit,
            truth_graph_sha256 = model.TruthGraphSha256,
            raw_lean_report_sha256 = model.RawLeanReportSha256,
            dag_md_sha256 = model.DagMdSha256,
            residual_frontier_sha256 = model.ResidualFrontierSha256,
            declarations_sha256 = model.DeclarationsSha256,
            frozen_ledger_head_hash = model.FrozenLedgerHeadHash,
            frozen_ledger_sequence = model.FrozenLedgerSequence,
        });
        var bytes = StructuredCanonicalWriter.WriteJson(element);
        if (SourceSnapshotJsonReader.Read(bytes.AsSpan()) != model)
        {
            throw new FormatException("Source snapshot writer did not preserve its input model.");
        }

        return bytes;
    }
}

/// <summary>
/// Fail-closed reader for <c>source-snapshot.v1.json</c>. It requires the exact v1 field set,
/// rejects duplicate or additional properties, and validates every Git object and SHA-256 identity.
/// </summary>
public static class SourceSnapshotJsonReader
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    private static readonly string[] Properties =
    [
        "dag_md_sha256",
        "declarations_sha256",
        "frozen_ledger_head_hash",
        "frozen_ledger_sequence",
        "lean_toolchain",
        "mathlib_rev",
        "producer_package_commit",
        "raw_lean_report_sha256",
        "residual_frontier_sha256",
        "schema",
        "source_commit",
        "source_repo",
        "source_tree",
        "truth_graph_sha256",
    ];

    public static SourceSnapshotModel Read(ReadOnlySpan<byte> bytes)
    {
        try
        {
            var text = StrictUtf8.GetString(bytes);
            using var document = JsonDocument.Parse(text);
            var root = document.RootElement;
            RequireProperties(root);

            var schema = String(root, "schema");
            if (schema != "source-snapshot.v1")
            {
                throw new FormatException("Source snapshot schema tag is not source-snapshot.v1.");
            }

            var sourceCommit = GitObjectId(root, "source_commit");
            var sourceTree = GitObjectId(root, "source_tree");
            TruthExportValidation.RequireSameGitObjectFormat(sourceCommit, sourceTree);

            return new SourceSnapshotModel(
                schema,
                String(root, "source_repo"),
                sourceCommit,
                sourceTree,
                String(root, "lean_toolchain"),
                GitObjectId(root, "mathlib_rev"),
                GitObjectId(root, "producer_package_commit"),
                Sha256Id(root, "truth_graph_sha256"),
                Sha256Id(root, "raw_lean_report_sha256"),
                Sha256Id(root, "dag_md_sha256"),
                Sha256Id(root, "residual_frontier_sha256"),
                Sha256Id(root, "declarations_sha256"),
                Sha256Id(root, "frozen_ledger_head_hash"),
                NonNegativeInteger(root, "frozen_ledger_sequence"));
        }
        catch (Exception exception) when (
            exception is JsonException or DecoderFallbackException or InvalidOperationException)
        {
            throw new FormatException("Source snapshot JSON is invalid.", exception);
        }
    }

    private static string GitObjectId(JsonElement parent, string name)
    {
        var value = String(parent, name);
        TruthExportValidation.RequireGitObjectId(value, name);
        return value;
    }

    private static string Sha256Id(JsonElement parent, string name)
    {
        var value = String(parent, name);
        TruthExportValidation.RequireSha256Id(value, name);
        return value;
    }

    private static string String(JsonElement parent, string name) =>
        parent.TryGetProperty(name, out var value) && value.ValueKind == JsonValueKind.String
            ? value.GetString() ?? throw new FormatException($"Source snapshot {name} is null.")
            : throw new FormatException($"Source snapshot {name} must be a string.");

    private static int NonNegativeInteger(JsonElement parent, string name) =>
        parent.TryGetProperty(name, out var value) && value.TryGetInt32(out var result) && result >= 0
            ? result
            : throw new FormatException($"Source snapshot {name} must be a non-negative integer.");

    private static void RequireProperties(JsonElement element)
    {
        if (element.ValueKind != JsonValueKind.Object)
        {
            throw new FormatException("Source snapshot must be an object.");
        }

        var actual = new HashSet<string>(StringComparer.Ordinal);
        foreach (var property in element.EnumerateObject())
        {
            if (!actual.Add(property.Name))
            {
                throw new FormatException($"Source snapshot property '{property.Name}' is duplicated.");
            }
        }

        if (actual.Count != Properties.Length || !actual.SetEquals(Properties))
        {
            throw new FormatException("Source snapshot has missing or unexpected fields.");
        }
    }
}
