using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037;

internal sealed class Branch2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Branch2.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full original cache step and bound for prefix 5335037, outcome 2",
        H("Full original cache step and bound for prefix 5335037, outcome 2"),
        Blocks(
            Paragraph(Text("Each Describe belongs to the actual source module and an existing named public declaration. The original Lean namespace, imports, options, statements and proofs are retained. Private receipts and private helpers receive no public wrappers.")),
            Paragraph(Text("This module belongs to the complete original context at depth eighteen, base-four prefix 5335037, node 442 and remaining fuel three. Its own parent cache, four children and partial assignment remain separate from the other prefixes reaching the same node.")),
            Paragraph(Text("At depth seventeen, prefix 1333759 and node 1305, this context is original outcome 1. Its complete accepted theorem supplies that ordered child to Raw002Tail442/Assembly.raw_cut_00337, which assembles the original context at depth thirteen, prefix 5209 and node 17413 together with every other original sibling along the four preceding outcome-three splits.")),
            Paragraph(Text("Complete-context acceptance retains this prefix's full prefix-cache equality, all four whole-cache steps, all four lower inequalities and original partial assignment. Shared node 442 fixes the replay node only. Reusing an opaque canonical row supplies its indexed full-row equality; the remaining State, cache and prefix-context obligations are earned separately for this prefix.")),
            Paragraph(Text("All thirty-two private placement declarations remain. Seventeen use this prefix's complete unchanged CachedLocal equalities and fifteen affected placements use its own exact local transitions. The two public results enter this prefix's all_steps and all_bounds.")),
            Node("branch2-step", "branch2_step", "Exact whole-cache step for outcome 2",
                "For prefix 5335037, updating the entire parentCache at original coordinate eighteen and outcome 2 equals the entire nextCache at that outcome. The proof retains every State and all four MirrorRow fields at all sixteen triangle and sixteen singleton placements.", DescribeRole.Theorem),
            Node("branch2-bound", "branch2_bound", "Original whole-cache lower inequality",
                "For prefix 5335037 and outcome 2, the original scale is at most lower of the entire nextCache. The proof projects to childCache2, uses its exact lower total 16997489943731115 and checks the integer inequality with scale 6987435. The separate exact step supplies the full cache transition.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
