using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class SharedArenaFiniteTemplatesDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/SharedArenaFiniteTemplates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Homogeneous finite-output readouts retain two causal slots for shared-arena registrations.",
        H("SharedArenaFiniteTemplates"),
        Blocks(
            Node("finite-signature", "finiteSignature", "Finite Boolean-indexed signature",
                "A Boolean-indexed signature gives both causal slots the common output Fin 16 and leaves the anchor family empty.", DescribeRole.Definition),
            Node("intervention-realization", "interventionFiniteRealization", "Intervention finite realization",
                "The supplied functions are retained as the false and true readouts of the homogeneous signature.", DescribeRole.Definition),
            Node("observation-realization", "observationFiniteRealization", "Observation finite realization",
                "The observation-intervention registrations use the same two-slot realization shape.", DescribeRole.Definition),
            Node("finite-arena", "finiteArena", "Finite separation law",
                "The law records a pair of states that agree on the first readout and differ on the second."))));

    private static DocumentBlock.Describe Node(
        string id, string declaration, string title, string explanation,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), role);
}
