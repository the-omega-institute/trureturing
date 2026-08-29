using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed class LeanCustomSyntaxCatalog(
    ImmutableDictionary<string, ImmutableArray<string>> importsByModule,
    ImmutableDictionary<string, ImmutableHashSet<string>> literalsByModule)
{
    internal IEnumerable<string> VisibleFrom(LeanSourceDeclaration declaration)
    {
        foreach (var literal in declaration.CustomSyntaxLiterals)
        {
            yield return literal;
        }

        var queue = new Queue<string>(declaration.Imports);
        var visited = new HashSet<string>(StringComparer.Ordinal);
        while (queue.TryDequeue(out var imported))
        {
            if (!visited.Add(imported))
            {
                continue;
            }

            if (literalsByModule.TryGetValue(imported, out var literals))
            {
                foreach (var literal in literals)
                {
                    yield return literal;
                }
            }

            if (importsByModule.TryGetValue(imported, out var transitive))
            {
                foreach (var next in transitive)
                {
                    queue.Enqueue(next);
                }
            }
        }
    }

    internal static ImmutableHashSet<string> ParseLiterals(
        ImmutableArray<LeanSourceToken> tokens,
        ImmutableArray<int> commandStarts)
    {
        var result = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        for (var index = 0; index < commandStarts.Length; index++)
        {
            var start = commandStarts[index];
            if (tokens[start].Text is not ("macro" or "syntax" or "notation" or "local" or "scoped"))
            {
                continue;
            }

            var end = index + 1 < commandStarts.Length ? commandStarts[index + 1] : tokens.Length;
            foreach (var token in tokens[start..end])
            {
                var literal = NormalizeLiteral(token.Text);
                if (token.Text.Length >= 2
                    && token.Text[0] == '"'
                    && token.Text[^1] == '"'
                    && literal.Length > 0)
                {
                    result.Add(literal);
                }
            }
        }

        return result.ToImmutable();
    }

    internal static string NormalizeLiteral(string value) =>
        (value.Length >= 2 && value[0] == '"' && value[^1] == '"'
            ? value[1..^1]
            : value).Trim();
}
