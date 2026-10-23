using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeActualStateSuppliersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateSuppliers.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The parent uses its original retained states, chosen child cycles and exact opening inventories throughout.",
        H("Retain Actual States While Supplying the Parent"),
        Blocks(
            Describe.Lean(DescribeId.Create("parent-from-state-suppliers"),
                DeclarationHandle.Create(Prefix + "parent_from_state_suppliers"),
                H("Choose the Parent and Its Actual Children Once"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("From complete old-order states with their parity flags, the construction chooses the special path and ordinary cycles once. The P child is attached to the specified old P state. The output saves these actual children, their literal openings, and the support and edge identities of the same parent cycle."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("state-parent-retention"),
                DeclarationHandle.Create(Prefix + "state_parent_retention"),
                H("Earn the Three Parent Edge Invariants"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same chosen parent cycle preserves every protected-a edge outside the protected pair, every remaining-b edge outside the enlarged selected set, and the selected-c restriction. Each conclusion is derived from the retained child states and their exact deleted opening edges."))), DescribeRole.Theorem))));
}
