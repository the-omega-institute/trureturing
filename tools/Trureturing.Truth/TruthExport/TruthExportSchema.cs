using System.Collections.Immutable;

namespace Trureturing.Truth;

/// One declaration inside a frozen node: its name key, kind, and content-addressed statement id.
public sealed record TruthExportDeclaration(
    string DeclarationNameKey,
    string Kind,
    string StatementId);

/// One STRICT-accepted active frozen node projected to plain wire fields. <see cref="NodeAxiomClosure"/>
/// is the node-level closure (the union over the node's declarations), distinct from any single
/// declaration's minimal closure. Every exported node is invariantly Closed, so there is no state field.
public sealed record TruthExportNode(
    string RepoPath,
    string FrozenNodeId,
    ImmutableArray<string> NodeAxiomClosure,
    ImmutableArray<TruthExportDeclaration> Declarations,
    ImmutableArray<string> PrerequisiteFrozenNodeIds);

/// <summary>
/// The plain, Engine-free wire model for the base's canonical truth-export. This package owns the shared
/// wire records plus the canonical reader/writer; the Engine-dependent projection from FrozenNodeMaterial
/// to these plain records stays in Scribe/base. <see cref="Create"/> canonicalises: it sorts the node set
/// by (repo_path, frozen_node_id), each node's axiom closure and prerequisite ids, and each node's
/// declarations by (name_key, statement_id), so byte output is a deterministic function of the frozen
/// content alone.
/// </summary>
public sealed record TruthExportModel(
    string Schema,
    int SchemaVersion,
    string Dialect,
    string SourceCommit,
    string SourceTree,
    string Producer,
    ImmutableArray<TruthExportNode> Nodes)
{
    /// Unversioned schema family.
    public const string SchemaName = "stratalint.truth-export";

    /// Versioned wire dialect; downstream consumers pin this as the only stable anchor.
    public const string CanonicalDialect = "stratalint.truth-export.v1";

    /// Stable producer identity. A version STRING, never an engine DLL/MVID hash.
    public const string ProducerName = "TruthExportCommand";

    public static TruthExportModel Create(
        ImmutableArray<TruthExportNode> nodes,
        string sourceCommit,
        string sourceTree)
    {
        var canonical = nodes
            .Select(static node => node with
            {
                NodeAxiomClosure = node.NodeAxiomClosure
                    .OrderBy(static axiom => axiom, StringComparer.Ordinal)
                    .ToImmutableArray(),
                Declarations = node.Declarations
                    .OrderBy(static declaration => declaration.DeclarationNameKey, StringComparer.Ordinal)
                    .ThenBy(static declaration => declaration.StatementId, StringComparer.Ordinal)
                    .ToImmutableArray(),
                PrerequisiteFrozenNodeIds = node.PrerequisiteFrozenNodeIds
                    .OrderBy(static prerequisite => prerequisite, StringComparer.Ordinal)
                    .ToImmutableArray(),
            })
            .OrderBy(static node => node.RepoPath, StringComparer.Ordinal)
            .ThenBy(static node => node.FrozenNodeId, StringComparer.Ordinal)
            .ToImmutableArray();
        var model = new TruthExportModel(
            SchemaName,
            1,
            CanonicalDialect,
            sourceCommit,
            sourceTree,
            ProducerName,
            canonical);
        TruthExportValidation.RequireValidModel(model);
        return model;
    }
}
