using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public static class CanonicalValuesWriter
{
    public const string RelativePath = RepositoryPathPolicy.ValuesProjectionPath;
    public const string InputPath = "D5/X_Frontier/ValuesProducer.lean";
    public const string ScribeLockPath =
        "Meta/StrataLint/StrataLint.Scribe/packages.lock.json";
    public static ImmutableArray<string> InputPaths { get; } =
    [
        ValuesKernelDataLoader.LeanModulePath,
        InputPath,
        "Directory.Build.props",
        "Directory.Packages.props",
        ValuesKernelDataLoader.RelativePath,
        ScribeLockPath,
        "global.json",
    ];

    public static ImmutableArray<byte> Write(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var inputs = InputPaths.Select(path =>
            (Path: path, Sha256: Convert.ToHexStringLower(SHA256.HashData(
                File.ReadAllBytes(Path.Combine(repositoryRoot, path)))))).ToArray();
        var inputSha256 = CombinedInputSha256(inputs);
        var definitions = ValuesKernelDataLoader.LoadRepository(repositoryRoot);
        var constants = definitions
            .OrderBy(static item => item.Id, StringComparer.Ordinal)
            .Select(Project)
            .ToArray();
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
                emitter_version = 2,
                input_sha256 = inputSha256,
                inputs = inputs.Select(static input => new
                {
                    path = input.Path,
                    sha256 = input.Sha256,
                }).ToArray(),
                projection = "D5/E/values--json",
                provenance = definitions.Select(static item => item.LeanGid).ToArray(),
            },
            constants,
            schema_version = 2,
        });
        return StructuredCanonicalWriter.WriteJson(document);
    }

    internal static string CombinedInputSha256(IEnumerable<(string Path, string Sha256)> inputs)
    {
        var material = "stratalint-scribe-values-input-v2\0" + string.Concat(
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
