using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class IffRegistrationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact iff registrations over finite object states.",
        H("IffRegistrations"),
        Blocks(
            Node("openArena", "The source state is one of the five assertion claims.", DescribeRole.Definition),
            Node("openRealization", "The readouts are open-outcome permission and the unsettled claim predicate.", DescribeRole.Definition),
            Node("open_bridge", "The bridge retains the exact open-permission iff for every claim.", DescribeRole.Theorem),
            Node("open_lawSensitive", "The frozen open-permission characterization satisfies the law; constant opposite predicates falsify it.", DescribeRole.Theorem),
            Node("open_slotSensitive", "Both Boolean readout slots have checked sensitivity witnesses.", DescribeRole.Theorem),
            Node("dualArena", "The source state is one of the four Boolean tie-breaking conventions.", DescribeRole.Definition),
            Node("dualRealization", "The readouts are duality fixedness and the two fixed-convention alternatives.", DescribeRole.Definition),
            Node("dual_bridge", "The bridge retains the exact dual-fixed iff for every convention.", DescribeRole.Theorem),
            Node("dual_lawSensitive", "The frozen dual-fixed characterization satisfies the law; constant opposite predicates falsify it.", DescribeRole.Theorem),
            Node("dual_slotSensitive", "Both Boolean readout slots have checked sensitivity witnesses.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/IffRegistrations." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
