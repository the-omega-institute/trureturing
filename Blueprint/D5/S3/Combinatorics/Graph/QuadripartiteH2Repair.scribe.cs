using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class QuadripartiteH2RepairDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/QuadripartiteH2Repair.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Boolean four-cube has a sharp degree-two repair coefficient of two; "
            + "the stronger exact matching-cost law remains open.",
        H("Four-cube coordinate geodesics"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("geodesic-boundary"),
                DeclarationHandle.Create(Prefix + "geodesic_boundary"),
                H("Coordinate geodesic boundary"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The four coordinate steps telescope in characteristic two, leaving "
                        + "the two endpoints."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("geodesic-weight"),
                DeclarationHandle.Create(Prefix + "geodesic_weight"),
                H("Coordinate geodesic weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each changed coordinate contributes exactly one supported triangular "
                    + "face."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("universal-repair"),
                DeclarationHandle.Create(Prefix + "universal_repair"),
                H("Sharp Boolean four-cube degree-two repair law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all natural p and q, every triangular cochain admits an edge "
                        + "repair with q times repaired support at most p times its "
                        + "defect count exactly when 2*q <= p. The upper proof pairs the "
                        + "even defect set along coordinate geodesics, bounds the filling "
                        + "by twice its size, and uses local characteristic-two exactness; "
                        + "the antipodal witness proves sharpness."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The exact equivalence preregistered in issue #11045 is not claimed here. "
                    + "Its matching-cost atoms remain residual open.")))));
}
