using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Riemannian;

internal sealed class ChartComparisonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Intrinsic metric and uniform pairwise chart comparison.",
        H("Fixed-basepoint Riemannian chart comparison"),
        Blocks(
            Paragraph(Text(
                "Let E be any finite-dimensional real inner-product space, including dimension zero, "
                + "and M a connected Hausdorff smooth manifold modeled on E, with its given continuous "
                + "Riemannian bundle. The canonical metric is constructed from this Riemannian data. "
                + "Finite-dimensional charts give local compactness; Hausdorffness then gives the separation "
                + "needed for the intrinsic emetric. Connectedness makes every intrinsic edistance finite: "
                + "the infinite-radius ball is nonempty and clopen. EMetricSpace.toMetricSpace preserves "
                + "the original topology definitionally. No completeness, minimizer, positive dimension "
                + "or independently supplied metric is assumed.")),
            Describe.Lean(
                DescribeId.Create("canonical-intrinsic-edistance"),
                DeclarationHandle.Create("D5/S3/Geometry/Riemannian/ChartComparison.canonicalMetric_edist"),
                H("Canonical intrinsic edistance"),
                StatementSource.FromAuthor(Disp(All("x", X("M"), All("y", X("M"),
                    new Formula.Relation(Call("canonicalEdist", X("x"), X("y")), FormulaRelationOperator.Equal,
                        Call("riemannianEDist", X("x"), X("y"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("canonicalEdist is edist after installing Original172.canonicalMetric. "
                    + "This definitional bridge is consumed by the pairwise comparison below."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-pairwise-chart-comparison"),
                DeclarationHandle.Create("D5/S3/Geometry/Riemannian/ChartComparison.canonical_pairwise_local_comparison"),
                H("One neighborhood for all pairs"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here phi=extChartAt p and Np(w) is the original g-norm of the actual differential "
                    + "of phi inverse at phi(p), applied to w. The source explicitly transports the dependent "
                    + "fiber norm along phi inverse(phi(p))=p. For each p and 0<epsilon<1, one open U containing "
                    + "p inside the chart source works for every x,y in U. The inequalities use canonicalMetric."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The live intermediate intrinsic_pairwise supplies the uniform fixed-Np comparison. "
                + "Relative tangent transport bounds give forward and inverse chart differential estimates "
                + "on a neighborhood V. Choose an intrinsic c-ball inside V, a convex chart ball whose inverse "
                + "lies in V, and shrink U so d(p,x)<c/4 and Np(phi(x)-phi(p))<c/(4(1-epsilon)). "
                + "A competitor shorter than the proposed lower bound has length<c/2; the triangle inequality "
                + "and subpath monotonicity put every point of it within intrinsic distance 3c/4 of p, hence "
                + "inside V. Integrating the fixed-norm forward differential estimate contradicts its shortness. "
                + "Competitors may leave U. The inverse image of the straight chart segment proves the upper bound. "
                + "The public theorem consumes this intermediate, the edistance bridge, and the explicit base-norm transport.")),
            Paragraph(Text(
                "This is C0/C1 of the original section 17.2 program: a formal synthesis using the pinned "
                + "Mathlib Riemannian interfaces, without a literature novelty claim. C2-C6, R3, R5 and the "
                + "full section 17.2 remain unfinished. Escape registration requires separate faithful source "
                + "reconstruction and compiled variation/sensitivity evidence; this document makes no registration claim."))),
        []));

    private static Formula X(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Statement() => All("p", X("M"), All("epsilon", X("Real"),
        Call("Implies", Call("And", Call("LT", Num(0), X("epsilon")), Call("LT", X("epsilon"), Num(1))),
            Call("ExistsOpenNeighborhoodInChartSource", X("p"),
                Call("ForAllPairsInNeighborhood", X("x"), X("y"),
                    Call("LE", Multiply(Subtract(Num(1), X("epsilon")), Call("NpChartChord", X("x"), X("y"))), Call("canonicalDist", X("x"), X("y"))),
                    Call("LE", Call("canonicalDist", X("x"), X("y")), Multiply(Add(Num(1), X("epsilon")), Call("NpChartChord", X("x"), X("y")))))))));
}
