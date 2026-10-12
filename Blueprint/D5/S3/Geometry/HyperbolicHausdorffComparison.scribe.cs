using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class HyperbolicHausdorffComparisonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local Hausdorff comparison for the native hyperbolic three-space metric.",
        H("Hyperbolic Hausdorff comparison"),
        Blocks(
            Paragraph(Text(
                "The coordinate type carries its Euclidean subtype metric; the same points "
                + "in HyperbolicThreeSpace carry the frozen curvature-minus-one arsinh metric. "
                + "For a coordinate ball of radius r below its centre height h, the two distances "
                + "satisfy D ≤ (h+2r)d and d ≤ D/(h-r). Applying the pinned Hausdorff image "
                + "inequalities in both directions gives a local measure comparison for every subset. "
                + "The scalar lower estimate follows from x/(1+x) ≤ log(1+x) ≤ arsinh(x), "
                + "and the upper estimate follows from t ≤ sinh(t) for t ≥ 0.")),
            Describe.Lean(
                DescribeId.Create("local-hausdorff-comparison"),
                DeclarationHandle.Create("D5/S3/Geometry/HyperbolicHausdorffComparison.local_hausdorff_comparison"),
                H("Two-sided local measure comparison"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here U is UpperHalfSpace over the complex numbers, h=height(p), H3 is "
                    + "Mathlib's raw three-dimensional Hausdorff measure on the indicated metric "
                    + "type, and lift is the existing HyperbolicSpace constructor. Empty sets, "
                    + "nonmeasurable subsets and coincident points are included. The result uses "
                    + "Mathlib.MeasureTheory.Measure.Hausdorff at the project's pinned revision. "
                    + "This is a formal synthesis of standard distance and Hausdorff estimates, "
                    + "with no literature novelty claim."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "This supplies local metric-measure distortion on the same native model used by "
                + "LengthGramBody.shared_radial_body. It does not identify normalized volume: "
                + "Euclidean Haar normalization, the exact height^-3 density, the Jacobian of the "
                + "original three-affine-coordinate Gram body image, frame independence, positivity "
                + "and finiteness, and the finite strictly positive flat-boundary limit remain "
                + "separate obligations. The original positive six-length and all-six strict cosine "
                + "domain is unchanged. The tensor/path-distance calibration described in the owning "
                + "Library note is also not asserted by this comparison."))),
        []));

    private static Formula X(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula LE(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LT(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula H3(Formula s) => Call("hausdorffMeasure", Num(3), s);
    private static Formula Statement()
    {
        var p = X("p"); var r = X("r"); var s = X("s");
        var h = Call("height", p);
        var image = Call("image", Qualified("HyperbolicSpace", "mk"), s);
        var upper = Call("ofReal", Call("inv", Subtract(h, r)));
        var lower = Call("ofReal", Add(h, Multiply(Num(2), r)));
        var conclusions = Seq(
            LE(H3(s), Multiply(Pow(lower, Num(3)), H3(image))), Sp, Land, Sp,
            LE(H3(image), Multiply(Pow(upper, Num(3)), H3(s))));
        return All("p", X("U"), All("r", X("Real"),
            Imp(LT(Num(0), r), Imp(LT(r, h),
            All("s", Call("Set", X("U")),
                Imp(Call("Subset", s, Call("ball", p, r)), conclusions))))));
    }
    private static Formula Pow(Formula a, Formula b) => Seq(Open, a, Close, Caret, Grp(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Close, Sp, F.Implies, Sp, Open, b, Close);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(X(owner), Dot, X(name)));
}
