using System.Collections.Immutable;

namespace Trureturing.Truth;

public static class TruthExportValidation
{
    // Exact output alphabet of tools/lean-inspector/Inspector.lean kindOf. The Engine's
    // CanonicalStatementWriter and the Engine-to-wire projection copy these values unchanged.
    public static readonly ImmutableHashSet<string> DeclarationKinds =
        ImmutableHashSet.Create(
            StringComparer.Ordinal,
            "axiom",
            "constructor",
            "def",
            "inductive",
            "opaque",
            "quotient",
            "recursor",
            "theorem");

    public static void RequireGitObjectId(string value, string field)
    {
        if (value is null || (value.Length != 40 && value.Length != 64) || !IsLowerHex(value))
        {
            throw new FormatException(
                $"Truth export {field} must be exactly 40 or 64 lowercase hex characters.");
        }
    }

    public static void RequireSameGitObjectFormat(string commit, string tree)
    {
        if (commit is null
            || tree is null
            || commit.Length != tree.Length
            || (commit.Length != 40 && commit.Length != 64))
        {
            throw new FormatException("Truth export source commit and tree must use the same Git object format.");
        }
    }

    public static void RequireRepoPath(string value)
    {
        if (string.IsNullOrEmpty(value)
            || value[0] == '/'
            || value[^1] == '/'
            || value.Contains('\\', StringComparison.Ordinal)
            || !value.EndsWith(".lean", StringComparison.Ordinal)
            || value.Any(static character => char.IsControl(character)))
        {
            throw new FormatException("Truth export repo_path is not a canonical relative POSIX Lean path.");
        }

        foreach (var segment in value.Split('/'))
        {
            if (segment.Length == 0 || segment is "." or "..")
            {
                throw new FormatException("Truth export repo_path contains a forbidden path segment.");
            }
        }
    }

    public static void RequireSha256Id(string value, string field)
    {
        const string prefix = "sha256:";
        if (value is null
            || value.Length != prefix.Length + 64
            || !value.StartsWith(prefix, StringComparison.Ordinal)
            || !IsLowerHex(value.AsSpan(prefix.Length)))
        {
            throw new FormatException(
                $"Truth export {field} must be exactly 'sha256:' followed by 64 lowercase hex characters.");
        }
    }

    public static void RequireKind(string value)
    {
        if (value is null || !DeclarationKinds.Contains(value))
        {
            throw new FormatException("Truth export declaration kind is unsupported.");
        }
    }

    internal static void RequireValidModel(TruthExportModel model)
    {
        ArgumentNullException.ThrowIfNull(model);
        if (model.Schema != TruthExportModel.SchemaName
            || model.SchemaVersion != 1
            || model.Dialect != TruthExportModel.CanonicalDialect
            || model.Producer != TruthExportModel.ProducerName)
        {
            throw new FormatException("Truth export schema, version, dialect, or producer is unsupported.");
        }

        RequireGitObjectId(model.SourceCommit, "source_commit");
        RequireGitObjectId(model.SourceTree, "source_tree");
        RequireSameGitObjectFormat(model.SourceCommit, model.SourceTree);

        var repoPaths = new HashSet<string>(StringComparer.Ordinal);
        var frozenNodeIds = new HashSet<string>(StringComparer.Ordinal);
        foreach (var node in model.Nodes)
        {
            RequireRepoPath(node.RepoPath);
            RequireSha256Id(node.FrozenNodeId, "frozen_node_id");
            if (!repoPaths.Add(node.RepoPath))
            {
                throw new FormatException("Truth export contains a duplicate repo_path.");
            }

            if (!frozenNodeIds.Add(node.FrozenNodeId))
            {
                throw new FormatException("Truth export contains a duplicate frozen_node_id.");
            }

            RequireStrictOrder(node.NodeAxiomClosure, "node axiom closure");
            TruthExportDeclaration? previousDeclaration = null;
            foreach (var declaration in node.Declarations)
            {
                if (declaration is null)
                {
                    throw new FormatException("Truth export declarations must not contain null entries.");
                }

                if (declaration.DeclarationNameKey is null)
                {
                    throw new FormatException("Truth export declaration_name_key must not be null.");
                }

                RequireSha256Id(declaration.StatementId, "statement_id");
                RequireKind(declaration.Kind);
                if (previousDeclaration is not null
                    && CompareDeclarations(previousDeclaration, declaration) >= 0)
                {
                    throw new FormatException("Truth export declarations must be sorted and unique.");
                }

                previousDeclaration = declaration;
            }

            foreach (var prerequisite in node.PrerequisiteFrozenNodeIds)
            {
                RequireSha256Id(prerequisite, "prerequisite_frozen_node_ids entry");
            }

            RequireStrictOrder(node.PrerequisiteFrozenNodeIds, "prerequisite frozen node ids");
        }

        RequireStrictOrder(
            model.Nodes.Select(static node => node.RepoPath + "\0" + node.FrozenNodeId),
            "nodes");

        foreach (var node in model.Nodes)
        {
            foreach (var prerequisite in node.PrerequisiteFrozenNodeIds)
            {
                if (!frozenNodeIds.Contains(prerequisite))
                {
                    throw new FormatException("Truth export prerequisite has no frozen-node endpoint.");
                }
            }
        }

        RequireAcyclic(model.Nodes);
    }

    private static void RequireAcyclic(ImmutableArray<TruthExportNode> nodes)
    {
        var remainingPrerequisites = nodes.ToDictionary(
            static node => node.FrozenNodeId,
            static node => node.PrerequisiteFrozenNodeIds.Length,
            StringComparer.Ordinal);
        var dependents = nodes.ToDictionary(
            static node => node.FrozenNodeId,
            static _ => new List<string>(),
            StringComparer.Ordinal);
        foreach (var node in nodes)
        {
            foreach (var prerequisite in node.PrerequisiteFrozenNodeIds)
            {
                dependents[prerequisite].Add(node.FrozenNodeId);
            }
        }

        var ready = new Queue<string>(remainingPrerequisites
            .Where(static pair => pair.Value == 0)
            .Select(static pair => pair.Key));
        var visited = 0;
        while (ready.TryDequeue(out var frozenNodeId))
        {
            visited++;
            foreach (var dependent in dependents[frozenNodeId])
            {
                remainingPrerequisites[dependent]--;
                if (remainingPrerequisites[dependent] == 0)
                {
                    ready.Enqueue(dependent);
                }
            }
        }

        if (visited != nodes.Length)
        {
            throw new FormatException("Truth export prerequisite graph contains a directed cycle.");
        }
    }

    private static void RequireStrictOrder(IEnumerable<string> values, string name)
    {
        string? previous = null;
        var hasPrevious = false;
        foreach (var value in values)
        {
            if (value is null)
            {
                throw new FormatException($"Truth export {name} must not contain null entries.");
            }

            if (hasPrevious && string.CompareOrdinal(previous, value) >= 0)
            {
                throw new FormatException($"Truth export {name} must be sorted and unique.");
            }

            previous = value;
            hasPrevious = true;
        }
    }

    private static int CompareDeclarations(
        TruthExportDeclaration left,
        TruthExportDeclaration right)
    {
        var nameComparison = string.CompareOrdinal(left.DeclarationNameKey, right.DeclarationNameKey);
        return nameComparison != 0
            ? nameComparison
            : string.CompareOrdinal(left.StatementId, right.StatementId);
    }

    private static bool IsLowerHex(ReadOnlySpan<char> value)
    {
        foreach (var character in value)
        {
            if (character is not ((>= '0' and <= '9') or (>= 'a' and <= 'f')))
            {
                return false;
            }
        }

        return true;
    }
}
