using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class ImplicationRegistrationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact implication registration programs over finite object states.",
        H("ImplicationRegistrations"),
        Blocks(
            Node("orbitObjectArena", "The object states are residues modulo thirty-one.", DescribeRole.Definition),
            Enumeration("orbitObjectArena", "31"),
            Node("orbitArena", "The implication template is instantiated on these object states.", DescribeRole.Definition),
            Node("orbit_slotSensitive", "Both CUT slots have independent checked law sensitivity.", DescribeRole.Theorem),
            Node("orbitRealization", "The two readouts evaluate the exceptional-residue test and the first orbit coordinate being one at the current state and every index.", DescribeRole.Definition),
            Node("orbit_bridge", "The bridge preserves the complete source statement using Boolean reflection and inserting or removing a Unit index only.", DescribeRole.Theorem),
            Node("orbit_lawSensitive", "The frozen theorem satisfies the law; a true antecedent with a false consequent falsifies it.", DescribeRole.Theorem),
            Node("gridObjectArena", "The object states are seventeen first grid coordinates; the readouts retain every second coordinate.", DescribeRole.Definition),
            Enumeration("gridObjectArena", "17"),
            Node("gridArena", "The implication template is instantiated on these object states.", DescribeRole.Definition),
            Node("grid_slotSensitive", "Both CUT slots have independent checked law sensitivity.", DescribeRole.Theorem),
            Node("gridRealization", "The two readouts evaluate odd parity and coverage at least twenty-four at the current state and every index.", DescribeRole.Definition),
            Node("grid_bridge", "The bridge preserves the complete source statement using Boolean reflection only, retaining both source binders.", DescribeRole.Theorem),
            Node("grid_lawSensitive", "The frozen theorem satisfies the law; a true antecedent with a false consequent falsifies it.", DescribeRole.Theorem),
            Node("profilesObjectArena", "The object states are eleven first vertices; the readouts retain every second vertex.", DescribeRole.Definition),
            Enumeration("profilesObjectArena", "11"),
            Node("profilesArena", "The implication template is instantiated on these object states.", DescribeRole.Definition),
            Node("profiles_slotSensitive", "Both CUT slots have independent checked law sensitivity.", DescribeRole.Theorem),
            Node("profilesRealization", "The two readouts evaluate distinct vertices and distinct link profiles at the current state and every index.", DescribeRole.Definition),
            Node("profiles_bridge", "The bridge preserves the complete source statement using Boolean reflection only, retaining both source binders.", DescribeRole.Theorem),
            Node("profiles_lawSensitive", "The frozen theorem satisfies the law; a true antecedent with a false consequent falsifies it.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Enumeration(string owner, string states) =>
        Describe.Example(
            DescribeId.Create(owner.ToLowerInvariant() + "-enumeration"), H(owner + " enumeration"),
            StrataLint.Scribe.FormulaDsl.Id("stateEnumeration"),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(owner + ".__state_enumeration gives the complete ascending " +
                states + "-state list used by the existing reflected counting route."))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/ImplicationRegistrations." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
