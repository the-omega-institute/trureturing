using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal sealed partial class LeanSourceCatalog
{
    private readonly ImmutableDictionary<string, RepositoryFile> sourceModules;

    private static string SourceIdentity(LeanSourceDeclaration source) =>
        (source.ManagedSourceClosure.IsDefaultOrEmpty ? "declaration\0" : "raw-source\0")
        + source.Path.Value + "\0" + source.FullName;

    private static bool HasOnlySingleQuotedOccurrences(ImmutableArray<LeanSourceToken> tokens, string name)
    {
        var found = false;
        for (var index = 0; index < tokens.Length; index++)
        {
            if (tokens[index].Text != name) continue;
            if (index == 0 || tokens[index - 1].Text != "`"
                || index > 1 && tokens[index - 2].Text == "`") return false;
            found = true;
        }
        return found;
    }

    private LeanSourceDeclaration? ResolveQuotedModuleSource(
        LeanSourceDeclaration context, LeanSourceDeclaration extractionOwner, string name)
    {
        if (!sourceModules.TryGetValue(name, out var source) || source.Path == context.Path
            || !IsImported(context, context with { Path = source.Path })) return null;
        return context with
        {
            FullName = "<quoted-module:" + name + ">",
            Kind = "quoted-module-source-closure", IsProof = false,
            SemanticTokens = [], AmbientTokens = [],
            ManagedSourceClosure = ReachableManagedSources(extractionOwner),
        };
    }

    private ImmutableArray<RepositoryFile> ReachableManagedSources(LeanSourceDeclaration owner)
    {
        var sources = ImmutableArray.CreateBuilder<RepositoryFile>();
        var queue = new Queue<string>([ModuleName(owner.Path)]);
        var visited = new HashSet<string>(StringComparer.Ordinal);
        while (queue.TryDequeue(out var module))
        {
            if (!visited.Add(module) || !sourceModules.TryGetValue(module, out var source)) continue;
            sources.Add(source);
            if (importsByModule.TryGetValue(module, out var imports))
                foreach (var import in imports) queue.Enqueue(import);
        }
        return sources.OrderBy(static source => source.Path.Value, StringComparer.Ordinal).ToImmutableArray();
    }

    private static void AppendManagedSourceClosure(StringBuilder output, LeanSourceDeclaration source, string role)
    {
        AppendField(output, role + "-kind", "managed-raw-source-closure");
        AppendField(output, role + "-name", source.FullName);
        foreach (var file in source.ManagedSourceClosure)
        {
            AppendField(output, "source-path", file.Path.Value);
            AppendField(output, "source-bytes", Convert.ToBase64String(file.RawBytes.AsSpan()));
        }
    }
}
