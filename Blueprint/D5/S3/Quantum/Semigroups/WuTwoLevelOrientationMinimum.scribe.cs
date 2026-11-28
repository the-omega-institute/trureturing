using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuTwoLevelOrientationMinimumDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuTwoLevelOrientationMinimum.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact scalar minimum used by the two-mode Wu orientation reduction.",
        H("Two-level orientation scalar minimum"),
        Blocks(
            Paragraph(Text(
                "The source defines axisQuadratic and productQuadratic on real variables, with the minimum theorems "
                + "imposing nonnegative squared-length hypotheses. axisArg selects the clipped scalar optimizer, axisMinimum evaluates that optimizer, and "
                + "twoModeMinimum is the smaller of the two axis minima.")),
            Entry("axis-lower", "axis_minimum_lower", "Axis minimum lower bound",
                "For nonnegative A and b, axisMinimum is at most axisQuadratic at every u in [0,1]."),
            Entry("axis-formula", "axis_minimum_formula", "Closed axis minimum formula",
                "For nonnegative A and b, axisMinimum equals C−b when A=0, "
                + "C+A/2−b²/(2A) when b≤A and A is nonzero, and C+A−b when b>A."),
            Entry("two-mode-exact", "twoMode_exact_minimum", "Exact product-simplex minimum",
                "For nonnegative mode coefficients and fields, twoModeMinimum lower-bounds every admissible "
                + "productQuadratic. An admissible product point attains equality, every admissible axis is above "
                + "twoModeMinimum, and one of the two axes attains it."),
            Entry("determinant-bound", "real_two_plane_determinant_bound", "Two-plane determinant bound",
                "The squared determinant of two real coordinate pairs is at most the product of their squared lengths."),
            Entry("physical-weight-bound", "real_two_plane_physical_weight_bound", "Weighted physical two-plane bound",
                "For nonnegative A₁ and A₂, twice the weighted sum of the absolute determinants of two real coordinate blocks "
                + "is at most the corresponding weighted sum of the four squared coordinate lengths."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
