using System.Collections.Immutable;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Scribe;

public static class TruthExportProjection
{
    public static TruthExportModel Project(
        ImmutableArray<FrozenNodeMaterial> closedNodes,
        ImmutableHashSet<RepoPath> frozenPaths,
        string sourceCommit,
        string sourceTree)
    {
        var nodes = closedNodes
            .Select(node => new TruthExportNode(
                node.RepoPath.Value,
                node.FrozenNodeId.Value,
                node.AxiomClosure,
                node.DeclarationStatementIds
                    .Select(static declaration => new TruthExportDeclaration(
                        declaration.DeclarationNameKey,
                        declaration.Kind,
                        declaration.StatementId.Value))
                    .ToImmutableArray(),
                node.PrerequisiteFrozenNodeIds
                    .Select(static id => id.Value)
                    .ToImmutableArray(),
                frozenPaths.Contains(node.RepoPath) ? "frozen" : "proven-not-yet-frozen"))
            .ToImmutableArray();

        return TruthExportModel.Create(nodes, sourceCommit, sourceTree);
    }
}
