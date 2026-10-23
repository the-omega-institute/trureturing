using System.Text.Json;
using System.Security.Cryptography;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.EngineeringScope;

// The inspector consumes this structured contract; utility header syntax has one parser.
internal static class LeanUtilityInputCommand
{
    // Managed Lean plus FILEMAP policy documents: enumeration follows the inputs, not the repository.
    private static readonly string[] Scope = ["D5", "Trureturing.lean", ":(glob)Meta/*"];
    private static readonly string[] ScopedInputs = ["D5", "Reg", "Trureturing.lean", ":(glob)Meta/*"];

    internal static ExplicitCommandResult Run(string repositoryRoot, IReadOnlyList<string> arguments) =>
        Run(() => GitRepositorySnapshotReader.ReadCurrent(repositoryRoot,
            readContents: arguments.Contains("--targets") ? LeanClosureValidator.IsReportLean : LeanClosureValidator.IsManagedLean,
            pathspecs: arguments.Contains("--targets") ? ScopedInputs : Scope), arguments);

    internal static ExplicitCommandResult Run(Func<RawRepositorySnapshot> readCurrent, IReadOnlyList<string> arguments)
    {
        var scopeOnly = arguments.Count > 0 && arguments[0] == "--scope";
        var remaining = scopeOnly ? arguments.Skip(1).ToArray() : arguments.ToArray();
        if (remaining.Length != 0 && (remaining.Length != 2 || remaining[0] != "--targets"))
            return new(2, string.Empty, "USAGE: StrataLint lean-utility-input [--scope] [--targets MODULES]\n");
        try
        {
            var snapshot = SnapshotDecoder.Decode(readCurrent()) switch
            {
                SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
                SnapshotDecodeOutcome.InfrastructureFailure failure => throw new FormatException(failure.Message),
            };
            var selected = remaining.Length == 0 ? null : LeanReportScope.Create(snapshot,
                remaining[1].Split((char[]?)null, StringSplitOptions.RemoveEmptyEntries)
                    .Select(static module => RepoPath.CreateKnown(module.Replace('.', '/') + ".lean")));
            var obligations = new List<object>();
            foreach (var (path, file) in snapshot.Files.OrderBy(static item => item.Key.Value, StringComparer.Ordinal))
            {
                if (selected is not null && !selected.Paths.Contains(path)) continue;
                if (!LeanClosureValidator.IsManagedLean(path.Value)
                    || !RepositoryRules.TryHeader(file.Text, out var header)
                    || !UtilitySyntax.TryParse(header.Utility, out var declaration, out _)
                    || declaration is null)
                    continue;
                if (scopeOnly)
                {
                    var inputModules = UtilityDeclarationValidator.DeclarationReferences(declaration)
                        .Select(static gid => LeanImportClosure.ModuleName(gid.Path))
                        .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
                    if (inputModules.Length > 0) obligations.Add(new { modulePath = path.Value, inputModules });
                    continue;
                }
                if (declaration is not { BasisKind: UtilityBasisKind.Refutes, Claim: { } claim, Result: { } result })
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
