using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;
internal sealed class DisjunctionRegistrationTemplatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "State-dependent disjunction registration templates.", H("DisjunctionRegistrationTemplates"), Blocks(
            Node("disjunctionSignature", "Two Boolean cut readouts represent the disjuncts.", DescribeRole.Definition),
            Node("disjunctionRealization", "Predicates are compiled into state-dependent Boolean readouts.", DescribeRole.Definition),
            Node("disjunctionArena", "An admissibility predicate carries the theorem hypotheses.", DescribeRole.Definition),
            Node("disjunctionLegacy", "The typed law is equivalent to the original disjunction statement.", DescribeRole.Theorem),
            Node("disjunction_sensitivity", "Each readout can change the law at an admissible state.", DescribeRole.Theorem))));
    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) => Describe.Lean(
        DescribeId.Create(declaration.Replace('_','-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/DisjunctionRegistrationTemplates." + declaration),
        H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
}
