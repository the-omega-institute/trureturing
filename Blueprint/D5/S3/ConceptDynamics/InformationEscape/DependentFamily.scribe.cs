using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class DependentFamilyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A generic dependent-family contract separates typed readouts from source binding and audit proofs.",
        H("DependentFamily"),
        Blocks(
            Node("signature", "Signature", "Dependent signature",
                "The five universe parameters t, s, r, o and a retain arbitrary Params, parameter-dependent State and role-and-parameter-dependent Output types. Only Role and Anchor carry finite enumerations; Role is nonempty. No finiteness or decidable equality is required of parameters, states or outputs."),
            Node("realization", "Realization", "Readouts and anchors",
                "A realization supplies one typed readout for every role and parameter, and one state in every parameter fiber for each anchor. These are mathematical operands, not registration evidence."),
            Node("realize", "realize", "Shared constructor",
                "The constructor stores the supplied readout and anchor families unchanged. Reg/Support/DependentFamily enrolls this common template; constructing a realization alone grants no enrollment."),
            Node("arena", "Arena", "Law over a realization",
                "An arena pairs a signature with a proposition-valued Law on its realizations. Consumer family definitions retain the complete source statement at the actual realization, including dependent hypotheses and conclusions."),
            Node("variation", "Variation", "Whole-family variation",
                "Variation requires Law actual and a realization bad with not Law bad. The intervention varies a whole family; it need not vary in every fiber, so degenerate fibers remain in the domain."),
            Node("sensitivity", "Sensitivity", "Live roles and anchors",
                "For each role, a law-breaking realization must keep every other readout and all anchors fixed at actual. For each anchor, a law-breaking realization must keep all readouts and every other anchor fixed. Empty anchor types make only the anchor clause vacuous."),
            Node("dependence", "ObservationalDependence", "Nonconstant actual observations",
                "Each role must have a parameter and two states in that same fiber with different actual outputs. Hypothetical variation cannot justify a constant actual readout; this requirement does not assert variation in every fiber."),
            Node("registration", "Registration", "Proof contract and source boundary",
                "The record requires an actual realization, an equivalence between the supplied statement and Law actual, variation, sensitivity and observational dependence. Source selection separately ties that statement to the original compiler declaration: coordinates, scoped occurrences, dependent binders, rigid universes and full statement reconstruction remain obligations of the source-binding consumer. A record alone does not establish source fidelity or enrollment."),
            Paragraph(Text("These are repository-derived schema definitions under Scribe provenance, with no novelty, coverage or freeze claim. Reg carries the audit proofs. A literal open residual records unknown residual information; it proves neither infinity, undecidability nor completeness and discharges none of the proof or binding obligations.")))));

    private static DocumentBlock.Describe Node(string id, string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/DependentFamily." + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
