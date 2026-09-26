using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Scribe;

public sealed record ValuesProjection(string Id, string RelativePath, ImmutableArray<byte> Bytes);

public static class CanonicalValuesWriter
{
    public static ImmutableArray<string> InputPaths { get; } = [ValuesKernelDataLoader.RelativePath];

    public static ImmutableArray<string> MutationKeys(string repositoryRoot) =>
        ValuesKernelDataLoader.LoadRepository(repositoryRoot).Select(static row => row.Id).ToImmutableArray();

    public static ImmutableArray<ValuesProjection> Write(string repositoryRoot) =>
        ValuesKernelDataLoader.LoadRepository(repositoryRoot).Select(WriteRow).ToImmutableArray();

    private static ValuesProjection WriteRow(ValueDefinition definition)
    {
        var document = JsonSerializer.SerializeToElement(new
        {
            attestation = new
            {
                consistency = new
                {
                    lean_binding = "gid+kind=def+std3+statement-sha256",
                    numeric_binding = "not-kernel-evaluated:noncomputable-real",
                },
                emitter = "StrataLint.Scribe.ValuesProducer",
                emitter_version = 3,
                projection = ValuesProjectionAddress.GidFor(definition.Id),
                provenance = definition.LeanGid,
            },
            constant = Project(definition),
            input = definition.NormalizedInput,
            schema_version = 3,
        });
        var projection = new ValuesProjection(definition.Id, ValuesProjectionAddress.PathFor(definition.Id),
            StructuredCanonicalWriter.WriteJson(document));
        ValidateBinding(projection);
        return projection;
    }

    // Validate our computed output, never use a tracked snapshot as a freshness oracle.
    public static void ValidateBinding(ValuesProjection projection)
    {
        using var parsed = JsonDocument.Parse(projection.Bytes.AsMemory());
        var root = parsed.RootElement;
        if (!ValuesProjectionAddress.TryIdFromPath(projection.RelativePath, out var id)
            || !string.Equals(id, projection.Id, StringComparison.Ordinal)
            || root.GetProperty("constant").GetProperty("id").GetString() != id
            || root.GetProperty("input").GetProperty("id").GetString() != id
            || root.GetProperty("attestation").GetProperty("projection").GetString()
                != ValuesProjectionAddress.GidFor(id))
            throw new FormatException("Values projection key, payload and path binding mismatch.");
    }

    private static object Project(ValueDefinition definition)
    {
        var evaluation = definition.Computation is null ? null : ValuesEvaluator.Evaluate(definition);
        return new
        {
            comparison = evaluation?.Comparison ?? "not-computed-open",
            @decimal = evaluation?.Decimal,
            definition = definition.Definition,
            error = evaluation?.Error,
            exact_value = definition.ExactValue,
            formula = definition.Formula,
            id = definition.Id,
            kernel_receipts = evaluation?.KernelReceipts.Select(static receipt => new
            {
                kernel = receipt.Kernel,
                parameters = receipt.Parameters,
                results = receipt.Results,
            }).ToArray() ?? [],
            lean_gid = definition.LeanGid,
            lean_statement_sha256 = definition.LeanStatementSha256,
            method = definition.Method,
            open_reason = definition.OpenReason,
            provenance = definition.LeanGid,
            reference_error = definition.ReferenceError,
            reference_value = definition.ReferenceValue,
            refs = definition.References,
            status = definition.Status is ValueDefinitionStatus.Emitted ? "emitted" : "registered-open",
            value = evaluation?.Value,
        };
    }
}
