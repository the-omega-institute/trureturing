using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState;

internal sealed class Branch1Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Branch1.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full original cache step and lower bound for outcome 1",
        H("Full original cache step and lower bound for outcome 1"),
        Blocks(
            Paragraph(Text("This document follows the actual source owner; the existing Lean namespace and all mathematical source are retained. Only already named public declarations receive Describe nodes. Private proofs, the anonymous instance and transient examples receive no new wrappers.")),
            Paragraph(Text("The production connection uses the complete original context at depth eighteen, base-four prefix 5335038 and node 442. Raw002Tail442/Assembly.raw_cut_00337 consumes that context along the original path from depth thirteen, prefix 5209 and node 17413. Its unchanged Raw002 response enters Responses110 and the original score lower-bound consumer.")),
            Paragraph(Text("Metadata preparation does not assert a successful compile, scoped report, Scribe emission, complete producer acceptance or global score bound. The other original sibling contexts and remaining producer components retain their separate proof obligations.")),
            Paragraph(Text("All thirty-two private placement declarations remain: seventeen use shared entire CachedLocal equalities from UnchangedRows, and fifteen affected placements use their exact local transition receipts. FullLocalFields retains the complete State and all four MirrorRow fields. The lower proof projects nextCache to childCache1, rewrites its exact signed thirty-two-row total from LowerBounds, and compares that total with the unchanged scale 6987435. CanonicalState/Accepted consumes both public results through all_steps and all_bounds.")),
            Node("branch1-step", "branch1_step", "Exact original whole-cache step for outcome 1",
                "Updating the complete parentCache at original coordinate eighteen and outcome 1 equals the complete nextCache at that outcome, in all sixteen triangle and sixteen singleton placements.", DescribeRole.Theorem),
            Node("branch1-bound", "branch1_bound", "Original lower inequality for outcome 1",
                "The unchanged original scale 6987435 is at most lower of the entire nextCache for outcome 1. The proof reduces the outcome projection to childCache1, uses LowerBounds.child1_lower_exact to obtain the exact total 1714852503522795, and checks the integer inequality. The whole-cache step remains a separate premise.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
