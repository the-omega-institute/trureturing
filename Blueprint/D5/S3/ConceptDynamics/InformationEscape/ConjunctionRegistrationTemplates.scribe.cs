using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class ConjunctionRegistrationTemplatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Typed finite conjunction registration programs preserve complete source statements.",
        H("ConjunctionRegistrationTemplates"),
        Blocks(
            Node("ConjunctionClause", "Finite indices give a closed language of count equality, three-set coverage, disjointness, positive and negative anchored membership, and binary conjunction. No constructor accepts an arbitrary law.", DescribeRole.Definition),
            Node("conjunctionStatement", "The interpreter retains the clause tree and the original finite set operations over predicates and anchors.", DescribeRole.Definition),
            Node("conjunctionDecidable", "Structural recursion decides the interpreted finite clause tree.", DescribeRole.Definition),
            Node("conjunctionSignature", "The generated signature contains exactly the requested Boolean ADMIT readouts and ANCHOR slots.", DescribeRole.Definition),
            Node("conjunctionRealization", "Each state predicate is reflected to its Boolean readout; the supplied anchors are retained.", DescribeRole.Definition),
            Node("conjunctionArena", "An explicit finite object arena and a typed clause tree determine the realization-dependent law.", DescribeRole.Definition),
            Node("conjunctionLegacy", "Boolean reflection preserves every clause and its conjunction structure without using source theorem proofs.", DescribeRole.Theorem),
            Node("replaceConjunctionReadout", "One Boolean readout changes while all other readouts and every anchor stay fixed.", DescribeRole.Definition),
            Node("replaceConjunctionAnchor", "One anchor changes while every readout and each other anchor stay fixed.", DescribeRole.Definition),
            Node("conjunction_sensitivity", "A valid realization and one falsifying update per slot construct full finite slot sensitivity, including anchor support.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
