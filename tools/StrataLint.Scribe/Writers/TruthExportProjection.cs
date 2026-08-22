using System.Collections.Immutable;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Scribe;

public static class TruthExportProjection
{
    public static TruthExportModel Project(
        ImmutableArray<FrozenNodeMaterial> activeNodes,
        string sourceCommit,
        string sourceTree)
    {
        var nodes = activeNodes
            .Select(static node => new TruthExportNode(
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
                    .ToImmutableArray()))
            .ToImmutableArray();

        return TruthExportModel.Create(nodes, sourceCommit, sourceTree);
    }
}
