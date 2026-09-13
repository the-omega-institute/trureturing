using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class PointwiseDisequalityRegistrationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact pointwise registration programs over finite object states.",
        H("PointwiseDisequalityRegistrations"),
        Blocks(
            Node("digitArena", "Both channel exclusions use the same four-digit object arena.", DescribeRole.Definition),
            Node("digit_slotSensitive", "Both readout slots carry checked sensitivity using digits zero and one.", DescribeRole.Theorem),
            Node("recurrentRealization", "The recurrent retraction and the excluded digit two remain separate readouts.", DescribeRole.Definition),
            Node("recurrent_bridge", "The bridge retains the original disequality at every digit.", DescribeRole.Theorem),
            Node("recurrent_lawSensitive", "The source theorem satisfies the law; equal constant readouts falsify it.", DescribeRole.Theorem),
            Node("transientRealization", "The transient retraction and the excluded digit zero remain separate readouts.", DescribeRole.Definition),
            Node("transient_bridge", "The bridge retains the original disequality at every digit.", DescribeRole.Theorem),
            Node("transient_lawSensitive", "The source theorem satisfies the law; equal constant readouts falsify it.", DescribeRole.Theorem))));

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
