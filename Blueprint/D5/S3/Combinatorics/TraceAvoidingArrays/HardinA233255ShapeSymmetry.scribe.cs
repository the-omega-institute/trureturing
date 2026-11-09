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
                + "scanner sector and anchored initial multiplicities are handled below.", DescribeRole.Theorem),
            Node("literal_canonical_bridge", "Original literal count at every positive height", "For every natural m, "
                + "the individual-array count at height m plus one equals 16 times 128 to the power m plus "
                + "32 times the sum of F at m over all sixteen actual canonical boundaries. "
                + "The unfinished scanner has seen colour one but not colour two. Its boundary is one of the "
                + "two alternating words on labels zero and one. There is exactly one compatible proper row "
                + "avoiding label two, with 128 lifts and the same suffix. Every row containing label two has "
                + "64 lifts and completes the scanner; all seven cells, including the discarded first cell, "
                + "participate in this test. Induction gives twice the unfinished continuation equal to the "
                + "completed continuation plus 128 to the power m. The anchored first-row fibres contribute "
                + "32 unfinished lifts at the alternating shape, 16 completed lifts there, and 32 completed "
                + "lifts at each other shape. These disjoint literal fibres yield the formula without an "
                + "orbit quotient. HardinA233255Recurrence proves the recurrence using an exact finite "
                + "vector certificate and unbounded polynomial propagation.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
