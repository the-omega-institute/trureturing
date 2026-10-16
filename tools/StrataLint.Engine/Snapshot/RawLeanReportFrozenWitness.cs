using System.Collections.Immutable;
using System.Text.Json;
using Trureturing.Truth;

namespace StrataLint.Engine;

internal static partial class RawLeanReportArtifact
{
    // Historical projections are untrusted commitments, never current Lean evidence.
    internal static FrozenStatementWitness ReadFrozenWitnessFile(string path) =>
        ReadFrozenWitness(File.ReadAllBytes(Path.GetFullPath(path)));

    internal static FrozenStatementWitness ReadFrozenWitness(ReadOnlySpan<byte> bytes)
    {
        using var document = ReadCanonicalDocument(bytes);
        var root = document.RootElement;
        RequireProperties(root, ["modules", "schema"], "historical Lean report");
        if (RequiredString(root, "schema") is not (Schema or ScopedSchema))
            throw new FormatException("Historical Lean report has an unsupported schema.");
        var modules = ImmutableDictionary.CreateBuilder<RepoPath, ImmutableArray<FrozenDeclarationStatement>>();
        string? previous = null;
        foreach (var item in RequiredArray(root, "modules").EnumerateArray())
        {
            var fields = new List<string> { "declarations", "imports", "module", "source_path", "source_sha256" };
            foreach (var field in new[] { "information_templates", "fib_analysis", "utility_refutation", "information_registration_errors" })
                if (item.TryGetProperty(field, out _)) fields.Add(field);
            RequireProperties(item, fields, "historical Lean module");
            var module = RequiredString(item, "module");
            RequireStrictOrder(previous, module, "historical modules");
            previous = module;
            var rawPath = RequiredString(item, "source_path");
            if (!RepoPath.TryCreate(rawPath, out var path) || !LeanClosureValidator.IsReportLean(rawPath)
                || ModuleName(rawPath) != module || !FrozenHashSyntax.IsSha256(RequiredString(item, "source_sha256")))
                throw new FormatException("Historical Lean module path or source hash is malformed.");
            _ = ReadSortedStrings(RequiredArray(item, "imports"), "historical imports");
            var declarations = ReadDeclarations(RequiredArray(item, "declarations"), materialArchive: null);
            foreach (var declaration in declarations)
                FrozenStateRecord.ValidateDeclarations([new FrozenDeclaration(declaration.NameKey, declaration.Kind)]);
            var projection = declarations.Where(static declaration => declaration.IncludeInStatement)
                .Select(static declaration => new FrozenDeclarationStatement(declaration.NameKey, declaration.Kind,
                    StatementId.Create(declaration.PrecomputedStatementId!))).ToImmutableArray();
            if (!modules.TryAdd(path, projection)) throw new FormatException("Historical Lean report has a duplicate path.");
        }
        return new FrozenStatementWitness(modules.ToImmutable());
    }
}
