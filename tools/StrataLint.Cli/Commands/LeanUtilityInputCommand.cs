using System.Text.Json;
using System.Security.Cryptography;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Cli;

// The inspector consumes this structured contract; utility header syntax has one parser.
internal static class LeanUtilityInputCommand
{
    internal static ExplicitCommandResult Run(IRepositoryGateway repository, IReadOnlyList<string> arguments)
    {
        if (arguments.Count != 0) return new(2, string.Empty, "USAGE: StrataLint lean-utility-input\n");
        try
        {
            var snapshot = SnapshotDecoder.Decode(repository.ReadCurrent()) switch
            {
                SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
                SnapshotDecodeOutcome.InfrastructureFailure failure => throw new FormatException(failure.Message),
            };
            var obligations = new List<object>();
            foreach (var (path, file) in snapshot.Files.OrderBy(static item => item.Key.Value, StringComparer.Ordinal))
            {
                if (!LeanClosureValidator.IsManagedLean(path.Value)
                    || !RepositoryRules.TryHeader(file.Text, out var header)
                    || !UtilitySyntax.TryParse(header.Utility, out var declaration, out _)
                    || declaration is not { BasisKind: UtilityBasisKind.Refutes, Claim: { } claim, Result: { } result })
                    continue;
                var claimTarget = (Target.Formal)claim.ToTarget();
                var resultTarget = (Target.Formal)result.ToTarget();
                if (!snapshot.Files.TryGetValue(claimTarget.Path, out var claimSource))
                    throw new FormatException($"Refutation claim source is absent: {claimTarget.Path.Value}.");
                obligations.Add(new
                {
                    modulePath = path.Value,
                    claimGid = claim.Value,
                    claimModule = LeanImportClosure.ModuleName(claimTarget.Path),
                    claimSelector = claimTarget.Declaration,
                    claimSourcePath = claimTarget.Path.Value,
                    claimSourceSha256 = "sha256:" + Convert.ToHexStringLower(SHA256.HashData(claimSource.RawBytes.AsSpan())),
                    resultGid = result.Value,
                    resultModule = LeanImportClosure.ModuleName(resultTarget.Path),
                    resultSelector = resultTarget.Declaration,
                });
            }

            return new(0, System.Text.Encoding.UTF8.GetString(
                StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(obligations)).AsSpan()), string.Empty);
        }
        catch (Exception exception) when (exception is FormatException or InvalidOperationException or ArgumentException or IOException)
        {
            return new(2, string.Empty, $"LEAN_UTILITY_INPUT_INVALID {exception.Message}\n");
        }
    }
}
