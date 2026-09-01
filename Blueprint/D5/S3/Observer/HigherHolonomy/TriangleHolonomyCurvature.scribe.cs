using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HigherHolonomy;

internal sealed class TriangleHolonomyCurvatureDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/HigherHolonomy/TriangleHolonomyCurvature.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triangle loops define a finite matrix curvature whose holonomy conjugates and whose trace and determinant are gauge invariant.",
        H("Finite Triangle Holonomy Curvature"),
        Blocks(
            Def("path", "trianglePath", "Oriented triangle path",
                "Three vertices determine the closed path from the first vertex through the second and third and back to the first."),
            Def("holonomy", "triangleHolonomy", "Triangle holonomy",
                "The finite path transport around the oriented triangle is its multiplicative holonomy."),
            Def("curvature", "triangleCurvature", "Triangle curvature defect",
                "Subtracting the identity matrix from triangle holonomy gives an additive curvature witness."),
            Def("flat", "IsFlatTriangle", "Flat triangle",
                "A triangle is flat when its loop holonomy is the identity unit."),
            Thm("formula", "triangle_holonomy_formula", "Ordered product formula",
                "Triangle holonomy is the return edge multiplied by the second edge and then the first edge."),
            Thm("gauge", "triangle_holonomy_gauge_conjugate", "Triangle holonomy is gauge conjugate",
                "All interior gauges telescope and only conjugation at the base vertex remains."),
            Thm("trace", "triangle_trace_gauge_invariant", "Triangle trace is gauge invariant",
                "The trace of triangle holonomy is unchanged by every vertex gauge."),
            Thm("det", "triangle_determinant_gauge_invariant", "Triangle determinant is gauge invariant",
                "The determinant of triangle holonomy is unchanged by every vertex gauge."),
            Thm("zero", "triangle_curvature_eq_zero_iff", "Zero curvature characterizes flatness",
                "The additive triangle curvature vanishes exactly when the loop holonomy is the identity."),
            Thm("flat-gauge", "isFlatTriangle_gauge", "Gauge transport preserves flatness",
                "A flat triangle remains flat after arbitrary vertex gauge transport."),
            Thm("backtrack", "backtrack_holonomy_eq_one", "Inverse-edge backtracking is trivial",
                "Traversing an edge and its prescribed inverse gives identity holonomy.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance")),
        ]));

    private static DocumentBlock.Describe Def(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Thm(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Theorem);
}
