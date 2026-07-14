using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public static class CanonicalValuesWriter
{
    public const string RelativePath = ValuesProjectionLoader.RelativePath;
    public const string InputPath = ValuesProjectionLoader.InputPath;
    public const string ScribeLockPath = ValuesProjectionLoader.ScribeLockPath;
    public static ImmutableArray<string> InputPaths { get; } = ValuesProjectionLoader.InputPaths;

    public static ImmutableArray<byte> Write(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var inputs = InputPaths.Select(path =>
            (Path: path, Sha256: Convert.ToHexStringLower(SHA256.HashData(
                File.ReadAllBytes(Path.Combine(repositoryRoot, path)))))).ToArray();
        var inputSha256 = CombinedInputSha256(inputs);
        var constants = ValuesDefinitions.All
            .OrderBy(static item => item.Id, StringComparer.Ordinal)
            .Select(Project)
            .ToArray();
        var document = JsonSerializer.SerializeToElement(new
        {
            attestation = new
            {
                emitter = "StrataLint.Scribe.ValuesProducer",
                emitter_version = 1,
                input_sha256 = inputSha256,
                inputs = inputs.Select(static input => new
                {
                    path = input.Path,
                    sha256 = input.Sha256,
                }).ToArray(),
                projection = "D5/E/values--json",
            },
            constants,
            schema_version = 1,
        });
        return StructuredCanonicalWriter.WriteJson(document);
    }

    internal static string CombinedInputSha256(IEnumerable<(string Path, string Sha256)> inputs)
    {
        var material = "stratalint-scribe-values-input-v1\0" + string.Concat(
            inputs.Select(static input => input.Path + "\0" + input.Sha256 + "\n"));
        return Convert.ToHexStringLower(SHA256.HashData(new UTF8Encoding(false, true).GetBytes(material)));
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
            method = definition.Method,
            open_reason = definition.OpenReason,
            reference_error = definition.ReferenceError,
            reference_value = definition.ReferenceValue,
            refs = definition.References,
            status = definition.Status is ValueDefinitionStatus.Emitted ? "emitted" : "registered-open",
            value = evaluation?.Value,
        };
    }
}
