using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeActualStatePromotionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStatePromotion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual P opening is recovered from the original retained P state and the same parent.",
        H("Promote the Original Actual P State"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-state-p-opening-inventory"),
                DeclarationHandle.Create(Prefix + "original_state_p_opening_inventory"),
                H("Recover the Actual P Opening Inventory"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The P opening used by the parent has the full support of its original P state and precisely that state cycle with the literal supplier edge removed. Restoring both old cut groups yields its exact joint-edge inventory."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-state-p-joint-split"),
                DeclarationHandle.Create(Prefix + "original_state_p_joint_split"),
                H("Split the Original Distinguished P Path"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The retained edge invariants force the literal two-edge P prefix on the distinguished path. Removing the supplier edge produces the exact inventory needed by the later closed-parent joint update; no new P walk is chosen."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("same-parent-chain"),
                DeclarationHandle.Create(Prefix + "same_parent_chain"),
                H("Keep the Saved Parent Chain Attached"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The saved child openings form the literal native c-linked chain from the retained parent base to its saved P opening, with the actual closing edge."))), DescribeRole.Theorem))));
}
