using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;
internal sealed class DisjunctionRegistrationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "State-dependent disjunction registrations.", H("DisjunctionRegistrations"), Blocks(
            Node("eisensteinArena", "The finite residue arena carries two Eisenstein norm alternatives.", DescribeRole.Definition),
            Node("eisenstein_bridge", "The residue theorem is equivalent to the disjunction law.", DescribeRole.Theorem),
            Node("eisenstein_lawSensitive", "The residue theorem satisfies the law and a constant false pair does not.", DescribeRole.Theorem),
            Node("eisenstein_slotSensitive", "Both residue readouts have checked slot sensitivity.", DescribeRole.Theorem))));
    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) => Describe.Lean(
        DescribeId.Create(declaration.Replace('_','-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/DisjunctionRegistrations." + declaration),
        H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
}
