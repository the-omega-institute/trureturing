using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FiniteAnnotatedSymmetryDAGDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/FiniteAnnotatedSymmetryDAG.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Static partial contexts with independently checked leaves",
        H("Static partial contexts with independently checked leaves"),
        Blocks(
            Paragraph(Text("Each annotated row identifies an actual partial assignment and a natural-number level. A rule table may share its branch shapes, but every bound certificate belongs to the actual row and assignment. At a split, all possible values are covered, the child level decreases strictly and the child's assignment equals the exact update of the parent's assignment. This representation avoids recursively evaluating cache transitions at a leaf; it does not remove the obligation to check every actual numerical leaf.")),
            Node("row", "Row", "A row carries its own actual partial context",
                "Assignment, level and bound, symmetry or split rule are explicit. Sharing a rule index supplies no assignment equality or arithmetic acceptance.", DescribeRole.Definition),
            Node("check-row", "checkRow", "Check a leaf or every annotated successor",
                "A bound row consumes its supplied Boolean certificate at the same index and assignment. A symmetry row checks dominance at that assignment. A split checks every value child for level descent and exact partial update.", DescribeRole.Definition),
            Node("smaller-bad-event", "checked_forces_smaller_bad_event", "A checked row forces a smaller bad event",
                "Assume each successful bound certificate bounds the original score of every compatible completion, each action preserves that score and each successful dominance check strictly decreases rank. Strong induction on the row level then excludes a bad bound completion or follows its actual value child to a symmetry cut. A symmetry cut yields a bad event of smaller rank; it does not itself establish a local score bound.", DescribeRole.Theorem),
            Node("global-bound", "checked_global_lower_bound", "All checked rows and an unknown root yield the global bound",
                "An all-unknown root admits every full event. Strong induction on the event's natural-number rank rules out every score below the same gap, using the row-level descent theorem. Complete row acceptance and all leaf soundness premises remain required.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
