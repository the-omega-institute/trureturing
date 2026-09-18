using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class PointwiseOrderRegistrationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact pointwise registration programs over finite object states.",
        H("PointwiseOrderRegistrations"),
        Blocks(
            Node("lengthZero", "The shared Fin 3 zero constant represents the strict lower bound in the realization and readout declaration.", DescribeRole.Definition),
            Node("lengthOne", "The Fin 3 one constant encodes the substitution length of false.", DescribeRole.Definition),
            Node("lengthTwo", "The shared Fin 3 two constant encodes the substitution length of true and the weak upper bound.", DescribeRole.Definition),
            Node("objectArena", "Both bounds quantify over the same Boolean substitution letter.", DescribeRole.Definition),
            Node("strictArena", "The positivity law compares Fin 3 codes using the strict branch of the homogeneous order arena.", DescribeRole.Definition),
            Node("weakArena", "The upper bound compares Fin 3 codes using the weak branch over the same object arena.", DescribeRole.Definition),
            Node("strict_slotSensitive", "Fin 3 values zero and one witness sensitivity of both slots for the strict law.", DescribeRole.Theorem),
            Node("weak_slotSensitive", "Fin 3 values zero and one witness sensitivity of both slots for the weak law.", DescribeRole.Theorem),
            Node("lengthReadout", "Boolean elimination returns Fin 3 code one at false and two at true; their natural values are the original substitution lengths.", DescribeRole.Definition),
            Node("positiveRealization", "The two readouts are the shared zero code and finite length code, also used by the explicit readout declaration.", DescribeRole.Definition),
            Node("positive_bridge", "Boolean cases identify each length code's natural value with the original list length. The defining Fin order transports strict positivity in both directions.", DescribeRole.Theorem),
            Node("positive_lawSensitive", "The source theorem satisfies the strict code law through the bridge; equal zero codes falsify it.", DescribeRole.Theorem),
            Node("upperRealization", "The two readouts are the finite length code and shared bound-two code, also used by the explicit readout declaration.", DescribeRole.Definition),
            Node("upper_bridge", "Boolean cases identify each length code's natural value with the original list length. The defining Fin order transports the weak upper bound in both directions.", DescribeRole.Theorem),
            Node("upper_lawSensitive", "The source theorem satisfies the weak code law through the bridge; constant codes one and zero falsify it.", DescribeRole.Theorem))));

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
