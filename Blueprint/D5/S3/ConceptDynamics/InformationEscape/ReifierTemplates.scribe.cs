using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class ReifierTemplatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform pointwise registration descriptor and generic evidence providers in the content plane.",
        H("ReifierTemplates"),
        Blocks(
            Node("pointwise", "The descriptor retains the carrier parameters and both supplied functions; its bridge from the complete pointwise equation to the generated law is a proved equivalence.", DescribeRole.Theorem),
            Node("sensitivity", "Arena nondegeneracy supplies an inhabited state, and a nontrivial output type supplies distinct values for the existing pointwise slot-sensitivity theorem.", DescribeRole.Theorem),
            Node("variation", "Sensitivity at a supplied readout slot yields a realization satisfying the law and another refuting it, by a classical case split without enumeration.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/ReifierTemplates." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
