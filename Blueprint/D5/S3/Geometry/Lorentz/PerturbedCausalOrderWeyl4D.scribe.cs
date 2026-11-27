using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class PerturbedCausalOrderWeyl4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D.";
    private static LibraryNoteRef Penrose => LibraryNoteRef.Create("D5/L/HilbertOperators/penrose1965planewaves");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quadratic vacuum plane wave has a quadruple principal null direction, " +
        "contracts transverse null screens, and increases the volume of an axial causal diamond.",
        H("Vacuum plane wave curvature and causal focusing"),
        Blocks(
            Paragraph(Text("In coordinates (u, v, x, y), the metric is −2 du dv + A(x²−y²) du² + dx² + dy². "
                + "The opposite transverse curvature components cancel in the Ricci tensor. The circular and hyperbolic transverse solutions give different changes to screen area and diamond volume.")),
            Result("metric-det", "metric_det", "Coordinate volume density",
                "Expansion along the first row gives determinant −1 at every coordinate point for every real amplitude. "
                + "The density of the metric volume in these coordinates is therefore one.",
                All("A", Field("R"), All("p", Op("Point"),
                    Rel(Call("det", Call("metric", F.Id("A"), F.Id("p"))), Eq, Seq(Minus, D(1)))))),
            Result("ricci-zero", "ricci_zero", "Vacuum Ricci tensor",
                "The coordinate connection is obtained by differentiating the metric and contracting with its inverse. "
                + "The antisymmetrized quadratic connection terms cancel. The lowered curvature is the difference of the squares of du∧dy and du∧dx, each weighted by A. "
                + "In the Ricci trace the only surviving candidates have both free indices along u and contribute −A and A."),
            Result("weyl-pair-matrix", "waveWeyl_pairMatrix", "Curvature in the orthonormal pair basis",
                "Pulling back the coordinate curvature to the oriented orthonormal frame gives electric block diag(−A/2,A/2,0), "
                + "equal mixed blocks with off-diagonal entries A/2 in positions (1,2) and (2,1), and spatial block equal to the negative electric block."),
            Result("wave-quartic", "wave_quartic", "Exact Weyl quartic",
                "Evaluate the imported Weyl quartic on the complex null screens. In the oriented pair basis the two wedge blocks differ by the scalar −i. "
                + "Expanding the resulting quadratic form gives −4AZ⁴. Agreement at every complex Z gives polynomial equality.",
                All("A", Field("R"), Rel(Call("weylQuarticEquiv", Call("waveWeyl", F.Id("A"))), Eq,
                    Seq(Call("C", Seq(Minus, D(4), Sp, Cdot, Sp, F.Id("A"))), Sp, Cdot, Sp, Op("X"), Caret, Grp(D(4)))))),
            Result("wave-type-n", "wave_typeN", "Quadruple propagation ray",
                "For nonzero A the polynomial has the single finite zero Z=0 with multiplicity four and nonzero fourth coefficient. "
                + "The frame sends this chart generator to √2 times the v coordinate vector."),
            Result("null-geodesic", "nullGeodesic_spec", "Closed-form affine null geodesic",
                "For nonzero frequency ω with A=ω², the x coordinate is x₀ cosh(ωu)+α sinh(ωu)/ω. "
                + "The y coordinate is y₀ cos(ωu)+β sin(ωu)/ω. The v coordinate changes by half the increment in xx′+yy′. "
                + "Two differentiations give the affine connection equation, and a single differentiation of v gives zero metric speed."),
            Result("parallel-caustic", "parallel_first_caustic", "Parallel caustic",
                "For positive ω the determinant of the position Jacobian is positive for 0<u<π/(2ω). "
                + "At the endpoint the second diagonal entry is zero, while the first is the strictly positive cosh(π/2).",
                acknowledgePenrose: true),
            Result("vertex-caustic", "vertex_first_caustic", "Vertex caustic",
                "For positive ω the determinant of the velocity Jacobian is positive for 0<u<π/ω. "
                + "At the endpoint the second diagonal entry is zero, while the first is the strictly positive sinh(π)/ω.",
                acknowledgePenrose: true),
            Result("screen-area-contraction", "screen_area_contracts", "Strict transverse contraction",
                "The parallel determinant lies strictly between zero and one before the parallel caustic. Its second derivative with respect to ωu is −2 sin(ωu)sinh(ωu). "
                + "The vertex determinant lies strictly between zero and u² before the vertex caustic. The second derivative of t²−sin(t)sinh(t) is 2(1−cos(t)cosh(t))."),
            Result("vertex-area-asymptotic", "vertex_area_asymptotic", "Leading vertex area correction",
                "The Taylor coefficients of sin(t)sinh(t) through degree six are those of t²−t⁶/90. "
                + "On the punctured neighborhood of zero, division by t² gives relative area 1−t⁴/90 with remainder o(t⁴)."),
            Result("axial-diamond-volume", "axial_diamond_volume", "Strict excess of axial diamond volume",
                "Take axial tips (0,0,0,0) and (T,V,0,0), with ω>0, T>0, ωT<π and V>0. "
                + "The minimum longitudinal increments on the two timelike segments are quadratic in the transverse endpoint. "
                + "Their sum has coefficients Kx=ω(coth(ωu)+coth(ω(T−u))) and Ky=ω(cot(ωu)+cot(ω(T−u))) in the two directions. "
                + "Integrating the available longitudinal height V−(Kx x²+Ky y²)/2 over its positive ellipse gives πV²/√(KxKy). "
                + "Write r(t)=sin(t)sinh(t)/t² with r(0)=1. The logarithm of r is strictly concave before π, so the slice ratio √(r(ωu)r(ω(T−u))/r(ωT)) exceeds one. "
                + "Integration over u gives a four-volume strictly above the flat value πV²T²/6.")),
        []));

    private static DocumentBlock Result(string id, string name, string title, string prose,
        Formula? formula = null, bool acknowledgePenrose = false) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
        formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(Disp(formula)),
        acknowledgePenrose ? AssessedProvenance.FromRepo(Penrose) : AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Field(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Op(name), [.. args]);
    private static Formula Rel(Formula a, Formula rel, Formula b) => Seq(a, Sp, rel, Sp, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
}
