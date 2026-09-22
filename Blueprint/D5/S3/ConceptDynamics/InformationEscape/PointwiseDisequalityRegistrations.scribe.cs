using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class PointwiseDisequalityRegistrationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact pointwise registration programs over finite object states.",
        H("PointwiseDisequalityRegistrations"),
        Blocks(
            Node("digitZero", "The Fin 4 zero constant is shared by the recurrent table and the transient exclusion readout.", DescribeRole.Definition),
            Node("digitOne", "The Fin 4 one constant is the transient table value at input zero.", DescribeRole.Definition),
            Node("digitTwo", "The Fin 4 two constant is shared by the recurrent table decision and its excluded readout.", DescribeRole.Definition),
            Node("digitArena", "Both channel exclusions use the same four-digit object arena and homogeneous Fin 4 outputs.", DescribeRole.Definition),
            Node("digit_slotSensitive", "Both readout slots carry checked sensitivity using digits zero and one.", DescribeRole.Theorem),
            Node("recurrentReadout", "Boolean elimination implements the table [0, 1, 0, 3] on inputs [0, 1, 2, 3], replacing only digit two by zero.", DescribeRole.Definition),
            Node("recurrentRealization", "The table readout and shared excluded digit two are the two homogeneous outputs, also used by the explicit readout declaration.", DescribeRole.Definition),
            Node("recurrent_bridge", "Checking all four inputs proves the table equals the original recurrent retraction; rewriting this identity recovers the original disequality at every digit.", DescribeRole.Theorem),
            Node("recurrent_lawSensitive", "The source theorem satisfies the table law through the bridge; two constant digit-two readouts falsify it.", DescribeRole.Theorem),
            Node("transientReadout", "Boolean elimination implements the table [1, 1, 2, 3] on inputs [0, 1, 2, 3], replacing only zero by one.", DescribeRole.Definition),
            Node("transientRealization", "The table readout and shared excluded digit zero are the two homogeneous outputs, also used by the explicit readout declaration.", DescribeRole.Definition),
            Node("transient_bridge", "Checking all four inputs proves the table equals the original transient retraction; rewriting this identity recovers the original disequality at every digit.", DescribeRole.Theorem),
            Node("transient_lawSensitive", "The source theorem satisfies the table law through the bridge; two constant zero readouts falsify it.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
