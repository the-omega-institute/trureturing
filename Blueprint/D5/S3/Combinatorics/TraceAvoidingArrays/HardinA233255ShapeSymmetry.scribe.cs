using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233255ShapeSymmetryDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical proper boundaries preserve every completed-scanner continuation height.",
        H("Relabelling complementary pairs after both distinguished colours appear"),
        Blocks(
            Paragraph(Text("When colours one and two have both appeared, every pair-label cell has "
                + "two individual-colour lifts. A seven-cell row therefore has multiplicity 128. "
                + "Permuting all three pair labels preserves each horizontal and antidiagonal inequality, "
                + "so the entire continuation transfer respects that permutation at every height.")),
            Node("proper", "Proper six-cell boundaries", "Adjacent labels differ.", DescribeRole.Definition),
            Node("Shape", "Canonical boundary representatives", "A proper six-cell word whose first two labels are zero and one.",
                DescribeRole.Definition),
            Node("canonical", "Canonical relabelling", "The first label becomes zero, the second becomes one, and the "
                + "remaining label becomes two. Properness makes the first two labels distinct.", DescribeRole.Definition),
            Node("completed_canonical_bridge", "All-height canonical correspondence", "Induction on continuation "
                + "height reindexes actual compatible pair rows by the same label permutation. The completed-scanner "
                + "continuation count therefore depends only on the canonical boundary. The initial and unfinished "
                + "scanner sectors still require their own weighted aggregation.", DescribeRole.Theorem),
            Node("representatives", "Sixteen actual canonical boundaries", "The explicit list contains every proper "
                + "six-cell boundary beginning zero, one, exactly once.", DescribeRole.Definition),
            Node("shapeEquiv", "Complete boundary enumeration", "A proved equivalence identifies the sixteen indices "
                + "with the actual canonical-boundary subtype, including representatives missing the third label.", DescribeRole.Definition),
            Node("classOf", "Successor class", "Normalize by first and second labels, then take the unique index "
                + "in the complete enumeration.", DescribeRole.Definition),
            Node("K", "Actual compatible-row matrix", "Entry i,j counts proper seven-cell pair rows compatible "
                + "with representative i whose six-cell suffix has canonical class j.", DescribeRole.Definition),
            Node("F", "Completed-scanner vector", "At height m this is 128 to the power m times K to the power m "
                + "applied to the all-ones vector.", DescribeRole.Definition),
            Node("completed_transfer_bridge", "Exact completed-state matrix powers", "For every natural continuation "
                + "height and every proper labelled six-cell boundary, the original completed-scanner continuation "
                + "equals F at its canonical class. The induction groups actual compatible pair rows by their "
                + "successor class. It does not presume a scalar count identity or fit a recurrence. The unfinished "
                + "scanner sector and anchored initial multiplicities are separate obligations.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
