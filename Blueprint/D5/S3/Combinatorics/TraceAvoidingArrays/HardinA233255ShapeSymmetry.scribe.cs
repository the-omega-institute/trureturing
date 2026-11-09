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
                + "scanner sectors still require their own weighted aggregation.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
