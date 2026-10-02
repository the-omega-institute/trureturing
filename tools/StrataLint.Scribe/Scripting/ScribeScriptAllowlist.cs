using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.Operations;

namespace StrataLint.Scribe;

/// <summary>Declaration IDs distinguish type use, individual members and audited repository types.</summary>
internal sealed class ScribeScriptAllowlist
{
    private readonly HashSet<string> types = new(StringComparer.Ordinal);
    private readonly HashSet<string> members = new(StringComparer.Ordinal);
    private readonly HashSet<string> wholeTypes = new(StringComparer.Ordinal);
    private readonly HashSet<string> formattedTypes = new(StringComparer.Ordinal);

    private readonly Dictionary<(string Member, string Parameter), HashSet<string>> constants = new();
    private readonly Dictionary<(string Member, int Ordinal), HashSet<string>> typeArguments = new();

    internal static (ScribeScriptAllowlist? Table, ScribeScriptFailure? Failure) Read(
        CSharpCompilation compilation, string entry, string? overridePath)
    {
        var path = overridePath ?? Path.Combine(AppContext.BaseDirectory, "Scripting", "ScribeScriptAllowlist.txt");
        string[] lines;
        try { lines = File.ReadAllLines(path); }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException)
        {
            return (null, Configuration(entry, $"script allowlist could not be read: {exception.Message}"));
        }
        var table = new ScribeScriptAllowlist();
        var seen = new HashSet<string>(StringComparer.Ordinal);
        for (var index = 0; index < lines.Length; index++)
        {
            var line = lines[index].Trim();
            if (line.Length == 0 || line.StartsWith('#')) continue;
            if (line.StartsWith("type-argument ", StringComparison.Ordinal))
            {
                var parts = line.Split(' ');
                if (parts.Length != 4 || parts.Any(string.IsNullOrEmpty) || !seen.Add(line)) return Invalid();
                var methods = DocumentationCommentId.GetSymbolsForDeclarationId(parts[1], compilation);
                if (methods.Length != 1 || methods[0] is not IMethodSymbol method || Id(method) != parts[1]) return Invalid();
                var parameter = method.TypeParameters.SingleOrDefault(item => item.Name == parts[2]);
                var allowed = new HashSet<string>(StringComparer.Ordinal);
                if (parameter is null || !table.typeArguments.TryAdd((parts[1], parameter.Ordinal), allowed)) return Invalid();
                foreach (var typeId in parts[3].Split(','))
                {
                    var typeSymbols = DocumentationCommentId.GetSymbolsForDeclarationId(typeId, compilation);
                    if (!allowed.Add(typeId) || typeSymbols.Length != 1 || typeSymbols[0] is not INamedTypeSymbol { Arity: 0 } type
                        || Id(type) != typeId) return Invalid();
                }
                continue;
            }
            if (line.StartsWith("constant ", StringComparison.Ordinal))
            {
                var parts = line.Split(' ');
                if (parts.Length != 4 || parts.Any(string.IsNullOrEmpty) || !seen.Add(line)) return Invalid();
                var methods = DocumentationCommentId.GetSymbolsForDeclarationId(parts[1], compilation);
                if (methods.Length != 1 || methods[0] is not IMethodSymbol method || Id(method) != parts[1]) return Invalid();
                var parameter = method.Parameters.SingleOrDefault(item => item.Name == parts[2]);
                var ids = parts[3].Split(',');
                var allowed = new HashSet<string>(StringComparer.Ordinal);
                if (parameter is null || !table.constants.TryAdd((parts[1], parts[2]), allowed)) return Invalid();
                foreach (var constant in ids)
                {
                    var fields = DocumentationCommentId.GetSymbolsForDeclarationId(constant, compilation);
                    if (!allowed.Add(constant) || fields.Length != 1 || fields[0] is not IFieldSymbol { HasConstantValue: true } field
                        || Id(field) != constant || !SymbolEqualityComparer.Default.Equals(field.Type, parameter.Type)) return Invalid();
                }
                continue;
            }
            var mode = line.StartsWith("all ", StringComparison.Ordinal) ? "all"
                : line.StartsWith("format ", StringComparison.Ordinal) ? "format" : "symbol";
            var id = mode == "symbol" ? line : line[(mode.Length + 1)..];
            if (!seen.Add(line) || id.Length < 3 || id[1] != ':'
                || id[0] is not ('T' or 'M' or 'P' or 'F') || mode != "symbol" && id[0] != 'T')
                return Invalid();
            var resolved = DocumentationCommentId.GetSymbolsForDeclarationId(id, compilation);
            if (resolved.Length != 1 || Id(resolved[0]) != id) return Invalid();
            var symbol = resolved[0];
            switch (mode)
            {
                case "all":
                    if (symbol is not INamedTypeSymbol || !IsRepository(symbol)) return Invalid();
                    table.wholeTypes.Add(id);
                    break;
                case "format":
                    if (symbol is not INamedTypeSymbol) return Invalid();
                    table.formattedTypes.Add(id);
                    break;
                default:
                    if (symbol is INamedTypeSymbol) table.types.Add(id);
                    else if (symbol is IMethodSymbol or IPropertySymbol or IFieldSymbol) table.members.Add(id);
                    else return Invalid();
                    break;
            }
            (ScribeScriptAllowlist?, ScribeScriptFailure?) Invalid() =>
                (null, Configuration(entry, $"script allowlist line {index + 1} is invalid or unavailable: {line}"));
        }
        if (table.types.Count + table.members.Count + table.wholeTypes.Count == 0)
            return (null, Configuration(entry, "script allowlist is empty"));
        if (table.formattedTypes.Any(id => !table.types.Contains(id) && !table.wholeTypes.Contains(id)))
            return (null, Configuration(entry, "implicit formatting requires a type-use entry"));
        if (table.constants.Any(item => !table.members.Contains(item.Key.Member)
            || item.Value.Any(id => !table.members.Contains(id))))
            return (null, Configuration(entry, "parameter constants require exact member and constant entries"));
        if (table.typeArguments.Any(item => !table.members.Contains(item.Key.Member)
            || item.Value.Any(id => !table.types.Contains(id) && !table.wholeTypes.Contains(id))))
            return (null, Configuration(entry, "type argument constraints require exact member and type-use entries"));
        return (table, null);
    }

    internal bool AllowsType(ITypeSymbol type) => Id(type) is { } id
        && (types.Contains(id) || wholeTypes.Contains(id));

    internal bool AllowsMember(ISymbol symbol) => Id(symbol) is { } id
        && (members.Contains(id) || symbol.ContainingType is { } type && wholeTypes.Contains(Id(type)!));

    internal bool AllowsFormatting(ITypeSymbol type) => Id(type) is { } id && formattedTypes.Contains(id);

    internal bool AllowsTypeArguments(ISymbol symbol)
    {
        if (symbol is not IMethodSymbol method || Id(method) is not { } id) return true;
        method = method.ReducedFrom ?? method;
        foreach (var constraint in typeArguments.Where(item => item.Key.Member == id))
            if (constraint.Key.Ordinal >= method.TypeArguments.Length
                || Id(method.TypeArguments[constraint.Key.Ordinal]) is not { } argument
                || !constraint.Value.Contains(argument)) return false;
        return true;
    }

    internal bool HasParameterConstraints(ISymbol symbol) => Id(symbol) is { } id
        && constants.Keys.Any(key => key.Member == id);

    internal bool AllowsArgument(IParameterSymbol? parameter, IOperation value)
    {
        if (parameter is null || Id(parameter.ContainingSymbol) is not { } id
            || !constants.TryGetValue((id, parameter.Name), out var allowed)) return true;
        return value is IFieldReferenceOperation { Field.HasConstantValue: true } field
            && value.ConstantValue.HasValue && Id(field.Field) is { } constant && allowed.Contains(constant);
    }

    internal static string? Id(ISymbol symbol)
    {
        if (symbol is IAliasSymbol alias) symbol = alias.Target;
        if (symbol is INamedTypeSymbol { IsTupleType: true } tuple) symbol = tuple.TupleUnderlyingType ?? tuple;
        if (symbol is IFieldSymbol field) symbol = field.CorrespondingTupleField ?? field;
        if (symbol is IMethodSymbol method) symbol = method.ReducedFrom ?? method;
        return symbol.OriginalDefinition.GetDocumentationCommentId();
    }

    internal static bool IsRepository(ISymbol symbol) =>
        symbol.ContainingAssembly?.Identity.Name is "StrataLint.Scribe" or "StrataLint.Engine";

    private static ScribeScriptFailure Configuration(string entry, string message) =>
        new(ScribeScriptFailureCode.HostConfiguration, entry, message);
}
