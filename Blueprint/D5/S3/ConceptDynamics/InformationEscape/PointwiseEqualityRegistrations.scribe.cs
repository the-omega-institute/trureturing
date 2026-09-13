using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class PointwiseEqualityRegistrationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact pointwise registration programs over finite object states.",
        H("PointwiseEqualityRegistrations"),
        Blocks(
            Node("substitutionArena", "The source state is the three-letter substitution label.", DescribeRole.Definition),
            Node("substitutionRealization", "The two readouts are the general and Tribonacci substitution expressions as stated.", DescribeRole.Definition),
            Node("substitution_bridge", "The bridge retains every label and both unreduced substitution expressions.", DescribeRole.Theorem),
            Node("substitution_lawSensitive", "The frozen compatibility theorem satisfies the law; empty and singleton readouts falsify it.", DescribeRole.Theorem),
            Node("substitution_slotSensitive", "The generic sensitivity theorem supplies checked support for both readouts.", DescribeRole.Theorem),
            Node("recenterArena", "The source state is one of the three directed neighbors.", DescribeRole.Definition),
            Node("recenterRealization", "The readouts are the recentered neighbor and the integer origin.", DescribeRole.Definition),
            Node("recenter_bridge", "The bridge retains the source equation at every direction without replacing its left side using the proof.", DescribeRole.Theorem),
            Node("recenter_lawSensitive", "The frozen recenter theorem satisfies the law; distinct constant coordinates falsify it.", DescribeRole.Theorem),
            Node("recenter_slotSensitive", "Both coordinate readout slots have checked sensitivity witnesses.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
