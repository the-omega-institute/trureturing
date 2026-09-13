using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class PointwiseOrderRegistrationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact pointwise registration programs over finite object states.",
        H("PointwiseOrderRegistrations"),
        Blocks(
            Node("objectArena", "Both bounds quantify over the same Boolean substitution letter.", DescribeRole.Definition),
            Node("strictArena", "The positivity law uses the strict branch of the order template.", DescribeRole.Definition),
            Node("weakArena", "The upper bound uses the weak branch over the same object arena.", DescribeRole.Definition),
            Node("strict_slotSensitive", "Both slots carry checked sensitivity for the strict law.", DescribeRole.Theorem),
            Node("weak_slotSensitive", "Both slots carry checked sensitivity for the weak law.", DescribeRole.Theorem),
            Node("positiveRealization", "The readouts retain zero and the stated substitution length.", DescribeRole.Definition),
            Node("positive_bridge", "The bridge preserves positivity at every Boolean letter.", DescribeRole.Theorem),
            Node("positive_lawSensitive", "The source theorem satisfies the strict law; equal zero readouts falsify it.", DescribeRole.Theorem),
            Node("upperRealization", "The readouts retain the stated substitution length and the bound two.", DescribeRole.Definition),
            Node("upper_bridge", "The bridge preserves the upper bound at every Boolean letter.", DescribeRole.Theorem),
            Node("upper_lawSensitive", "The source theorem satisfies the weak law; readouts one and zero falsify it.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/PointwiseOrderRegistrations." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
