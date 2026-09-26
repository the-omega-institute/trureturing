using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagSemantics.DepthFirst;

internal sealed class ExecutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shared-state DFS execution",
        H("Traversal execution"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("shared-state-execution"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/DagSemantics/DepthFirst/Execution.runs_iff_dfs_forest"),
                H("Execution and forest postorder"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The independent execution relation skips visited vertices, marks fresh vertices before traversing their children, and appends each fresh vertex after its children. It threads one visited state through child and sibling traversals. For every finite work list, finite-support initial visited dictionary and finite output accumulator, an execution exists exactly for the final visited state returned by the DFS forest construction and the initial accumulator followed by that forest's postorder. Cycles and duplicate roots or edges are allowed. An existing accumulator may already contain duplicates, and initial visitation may suppress a reachable subtree."))),
                DescribeRole.Theorem),
            Paragraph(Text("Interpreting DependenciesFirst through this relation requires the actual ordinally sorted root sequence, dependency-array order and duplicates, missing lookup as an empty list, equality-compatible lookup, a fixed finite snapshot and the stated collection-operation contracts. Exact dictionary equality here concerns Lean representations. The source correspondence is reviewed; this theorem does not certify a C# translator, exceptions, physical stack or memory bounds, CLR execution, or parser and producer completeness.")))));
}
