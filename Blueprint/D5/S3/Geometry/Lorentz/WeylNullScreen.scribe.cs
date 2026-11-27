using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class WeylNullScreenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/WeylNullScreen.";
    private static LibraryNoteRef Petrov => LibraryNoteRef.Create("D5/L/LieTheory/petrov1954weyl");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five distinct future null screens determine four-dimensional Weyl curvature, with exact rank for every finite family.",
        H("Weyl curvature from future null screens"),
        Blocks(
            Paragraph(Text(
                "How many future null directions determine Weyl curvature at a point? Five distinct directions suffice. "
                + "For N distinct directions the rank is min(10, 2N), and every family with at most four rays has a nonzero curvature witness in its kernel.")),
            Node("weyl-null-screen-sampling", "weyl_null_screen_sampling", "Exact rank and kernel dimension",
                "The linear map samples the complex Weyl tide at each ray, with its real and imaginary parts encoding the two independent transverse components. "
                + "At finite rays the contraction evaluates the degree-at-most-four polynomial. At infinity it reads the coefficient of z⁴. "
                + "For N at most five, Lagrange interpolation assigns arbitrary values at the finite nodes. If the family contains infinity, subtract the prescribed leading term and interpolate the finite residual values in degree at most three. "
                + "On any five rays the interpolation map is surjective between complex spaces of dimension five, so it is injective. For a larger family, restriction to five rays then gives injectivity. "
                + "The codomain has real dimension 2N. Rank–nullity gives the stated kernel dimension, including an empty family.",
                DescribeRole.Theorem, SamplingFormula()),
            Node("weyl-null-screen-five", "weyl_null_screen_five", "Reconstruction from any five rays",
                "The forward map takes the five tidal samples. The inverse interpolates the quartic from the samples in the same chart, then applies the inverse Weyl-to-quartic map. "
                + "Agreement at those five rays proves the two inverse laws.",
                DescribeRole.Definition),
            Node("weyl-null-screen-zero", "weyl_null_screen_zero", "Five vanishing tides force zero Weyl curvature",
                "The five-ray reconstruction implies that a Weyl matrix vanishes exactly when its five sampled tides vanish. "
                + "A nonzero Weyl tensor therefore has at most four distinct principal null directions, the rays on which its trace-free tide vanishes.",
                DescribeRole.Theorem, ZeroFormula(), acknowledgePetrov: true),
            Node("weyl-null-screen-vanishing", "weyl_null_screen_vanishing", "A nonzero witness for at most four rays",
                "For each finite node z in the sampled family, include a factor X−z and multiply the factors. The polynomial is monic, so its inverse Weyl image is nonzero. "
                + "If infinity is sampled, there are at most three finite factors, and the leading quartic coefficient vanishes. Repetitions are allowed. The empty family uses the constant polynomial 1.",
                DescribeRole.Theorem, VanishingFormula()),
            Node("complex-tide-weyl", "complexTide_weyl", "One complex component encodes the Weyl tide",
                "The real screen tidal matrix is symmetric, and its trace is the Ricci contraction on the null generator. "
                + "For Weyl curvature this trace vanishes. Expanding the complex contraction on the real and imaginary parts of the screen vector yields twice the first diagonal entry plus twice i times the off-diagonal entry.",
                DescribeRole.Theorem, ComplexTideFormula()),
            Node("weyl-quartic-eval", "weylQuarticEquiv_eval", "Quartic evaluation is the complex screen contraction",
                "At a finite ray the oriented bivector of the complex screen vector and null generator has blocks x and −ix, where x = (z²−1, −i(z²+1), 2z). "
                + "The Weyl block matrix then reduces the contraction to 2 xᵀ(E−iM)x. "
                + "Its expansion gives the quartic. The screen contracted at infinity gives exactly the fourth-degree coefficient.",
                DescribeRole.Theorem, QuarticEvaluationFormula()),
            Node("null-tidal-ricci-invariance", "null_tidal_ricci_invariance", "The trace-free null tide is the Weyl tide",
                "For each ordered pair of frame vectors, evaluate the Ricci decomposition on their wedges with the null generator k. "
                + "The Kulkarni–Nomizu terms containing the squared norm of k or its pairing with either frame vector vanish. "
                + "The scalar curvature term also vanishes because g(k,k) is zero. "
                + "In the displayed identity, T(Q,r,a,b) contracts curvature Q with the chosen generator and frame at r. W(R) is the Weyl projection of R, Ric(R,r) evaluates the Ricci tensor of R on (k,k), and delta is the frame metric. "
                + "Subtracting half the screen trace on the diagonal leaves the Weyl tide.",
                DescribeRole.Theorem, RicciInvarianceFormula()),
            Node("curvature-ricci-split", "curvature_ricci_split", "The Ricci and Weyl decomposition",
                "The bivector order is (01, 02, 03, 23, 31, 12), with metric diag(−1, 1, 1, 1). "
                + "The symmetric pair matrix satisfies the Bianchi equation tr(WC) = 0, where W exchanges the electric and spatial blocks. This trace is 2(C₀₁,₂₃ + C₀₂,₃₁ + C₀₃,₁₂). "
                + "Ricci contraction sums the components R(a,b,a,d) against the diagonal metric, with b and d free. "
                + "With S = Ric − r g/4 and r the Lorentzian trace of Ric, the inverse sends (C, S, r) to C + (g ⊙ S)/2 + r(g ⊙ g)/24. "
                + "The Kulkarni–Nomizu contraction is Ric(g ⊙ h) = 2h + tr_g(h)g. Hence the second term has Ricci S and the scalar term has Ricci rg/4.",
                DescribeRole.Definition),
            Node("weyl-electric-magnetic-equiv", "weyl_electric_magnetic_equiv", "Electric and magnetic coordinates",
                "In the oriented pair basis, write the symmetric curvature matrix in electric, mixed and spatial blocks E, M and N. "
                + "Ric₀₀ = tr E. The time–space Ricci entries are the skew differences of M. The spatial block of Ricci is −E + tr(N)Id − N. "
                + "Vanishing Ricci forces tr E = 0, M symmetric and N = −E. The Bianchi equation is tr M = 0. "
                + "Conversely every pair of real symmetric traceless three-by-three matrices E and M gives the Weyl matrix [[E, M], [M, −E]].",
                DescribeRole.Definition),
            Node("finrank-algebraic-curvature", "finrank_algebraicCurvature4", "Twenty algebraic curvature coordinates",
                "The split gives real dimension 20 = 10 + 9 + 1.",
                DescribeRole.Theorem, Equal(Dimension(Operator("AlgebraicCurvature4")), D(2, 0))),
            Node("finrank-weyl", "finrank_weyl4", "Ten real Weyl coordinates",
                "Five complex coordinates give real dimension ten.",
                DescribeRole.Theorem, Equal(Dimension(Operator("Weyl4")), D(1, 0))),
            Node("finrank-traceless-ricci", "finrank_tracelessRicci4", "Nine trace-free Ricci coordinates",
                "The six off-diagonal and three independent diagonal entries determine a symmetric trace-free Ricci form. The Lorentzian trace equation solves for its remaining diagonal entry.",
                DescribeRole.Theorem, Equal(Dimension(Operator("TracelessRicci4")), D(9))),
            Node("weyl-quartic-equiv", "weylQuarticEquiv", "Weyl curvature and quartic coefficients",
                "Use A = E − iM to give Weyl coordinates their complex scalar multiplication. "
                + "For A₁₁ = a, A₂₂ = b, A₁₂ = c, A₁₃ = d, A₂₃ = e and A₃₃ = −a−b, the coefficients in ascending order are "
                + "2(a−b)+4ic, −8d−8ie, −12(a+b), 8d−8ie and 2(a−b)−4ic. "
                + "Their first and last entries recover a−b and c, the middle entry recovers a+b, and the two odd entries recover d and e. "
                + "The inverse takes the real part of A for E and the negative imaginary part for M.",
                DescribeRole.Definition, acknowledgePetrov: true),
            Node("future-null-ray", "future_null_ray", "Unique positive rescaling",
                "A future null vector has positive time coordinate and zero Minkowski squared norm. "
                + "If its time plus third spatial coordinate is zero, nullity forces the first two spatial coordinates to vanish. "
                + "The vector lies on the ray at infinity with positive scale given by its time coordinate. "
                + "Otherwise the sum is positive, the scale is half the sum, and z is the first spatial coordinate plus i times the second, divided by the sum.",
                DescribeRole.Theorem, FutureRayFormula()),
            Node("null-generator-future", "nullGenerator_future", "The chart generators are future null",
                "The finite generator is (1+|z|², 2 Re z, 2 Im z, 1−|z|²), and the generator at infinity is (1, 0, 0, −1). "
                + "Each has positive time coordinate and zero Minkowski squared norm.",
                DescribeRole.Theorem, GeneratorFormula()),
            Node("screen-frame-spec", "screenFrame_spec", "The transverse frame is orthonormal",
                "The finite complex screen vector is (z, 1, i, −z), and the vector at infinity is (0, 1, −i, 0). "
                + "The chosen real frame consists of its real and imaginary parts. Both are orthogonal to the corresponding null generator and have unit norm and zero mutual inner product.",
                DescribeRole.Theorem, FrameFormula())),
        []));

    private static DocumentBlock Node(string id, string name, string title, string prose,
        DescribeRole role, Formula? formula = null, bool acknowledgePetrov = false) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
        formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(Disp(formula)),
        acknowledgePetrov ? AssessedProvenance.FromRepo(Petrov) : AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);

    private static Formula SamplingFormula()
    {
        Formula n = F.Id("N");
        Formula ray = F.Id("ray");
        Formula sample = Apply("nullTidalSample", ray);
        Formula ten = D(1, 0);
        Formula dataDimension = Seq(D(2), Sp, Cdot, Sp, n);
        Formula rank = Equal(Dimension(Apply("range", sample)), Apply("min", ten, dataDimension));
        Formula kernel = Equal(Dimension(Apply("ker", sample)), Apply("max", D(0), Subtract(ten, dataDimension)));
        return All("N", Field("N"),
            All("ray", RayFamily(n),
                Rel(Apply("Injective", ray), Implies, Rel(rank, Land, kernel))));
    }

    private static Formula ZeroFormula()
    {
        Formula ray = F.Id("ray");
        Formula c = F.Id("C");
        return All("ray", RayFamily(D(5)), Rel(Apply("Injective", ray), Implies,
            Parens(All("C", Operator("Weyl4"),
                Rel(Equal(Apply("nullTidalSample", ray, c), D(0)), Iff, Equal(c, D(0)))))));
    }

    private static Formula VanishingFormula()
    {
        Formula n = F.Id("N");
        Formula ray = F.Id("ray");
        Formula witness = Apply("vanishingWeyl", ray);
        return All("N", Field("N"), All("ray", RayFamily(n),
            Rel(Rel(n, Leq, D(4)), Implies,
                Rel(Equal(Apply("nullTidalSample", ray, witness), D(0)), Land,
                    Rel(witness, Neq, D(0))))));
    }

    private static Formula ComplexTideFormula()
    {
        Formula r = F.Id("r");
        Formula c = Apply("val", F.Id("C"));
        Formula t = Add(Tide(c, r, D(0), D(0)), Multiply(Operator("I"), Tide(c, r, D(0), D(1))));
        return All("C", Operator("Weyl4"), All("r", Operator("FutureNullRay"),
            Equal(Apply("complexTide", c, r), Multiply(D(2), Parens(t)))));
    }

    private static Formula QuarticEvaluationFormula()
    {
        Formula r = F.Id("r");
        Formula c = F.Id("C");
        return All("C", Operator("Weyl4"), All("r", Operator("FutureNullRay"),
            Equal(Apply("quarticEval", r, Apply("weylQuarticEquiv", c)),
                Apply("complexTide", Apply("val", c), r))));
    }

    private static Formula RicciInvarianceFormula()
    {
        Formula r = F.Id("r");
        Formula curvature = F.Id("R");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula tr = Add(Apply("T", curvature, r, D(0), D(0)), Apply("T", curvature, r, D(1), D(1)));
        Formula delta = Apply("delta", a, b);
        Formula ricci = Apply("Ric", curvature, r);
        Formula fullTide = Apply("T", curvature, r, a, b);
        Formula weylTide = Apply("T", Apply("W", curvature), r, a, b);
        Formula shift = Half(Multiply(delta, ricci));
        Formula tracePart = Half(Multiply(delta, Parens(tr)));
        return All("R", Operator("AlgebraicCurvature4"), All("r", Operator("FutureNullRay"),
            All("a", Apply("Fin", D(2)), All("b", Apply("Fin", D(2)),
                Rel(Equal(fullTide, Add(weylTide, shift)), Land,
                    Equal(Subtract(fullTide, tracePart), weylTide))))));
    }

    private static Formula Tide(Formula curvature, Formula ray, Formula a, Formula b) =>
        Apply("tidal", curvature, Apply("nullGenerator", ray),
            Apply("screenFrame", ray, a), Apply("screenFrame", ray, b));

    private static Formula Half(Formula n) => Seq(Frac, Grp(n), Grp(D(2)));

    private static Formula FutureRayFormula()
    {
        Formula v = F.Id("v");
        Formula p = F.Id("p");
        Formula scale = Apply("fst", p);
        Formula generator = Apply("nullGenerator", Apply("snd", p));
        Formula pairType = Rel(Field("R"), Times, Operator("FutureNullRay"));
        Formula positiveTime = Rel(D(0), Lt, App(v, D(0)));
        Formula nullity = Equal(Apply("minkowski", v, v), D(0));
        Formula decomposition = Equal(v, Rel(scale, Cdot, generator));
        Formula result = Rel(Rel(D(0), Lt, scale), Land, decomposition);
        return All("v", Arrow(Apply("Fin", D(4)), Field("R")), Rel(positiveTime, Implies,
            Rel(nullity, Implies,
                Seq(Exists, Bang, Sp, Parens(Seq(p, Colon, Sp, pairType)), Comma, Sp, result))));
    }

    private static Formula GeneratorFormula()
    {
        Formula r = F.Id("r");
        Formula k = Apply("nullGenerator", r);
        return All("r", Operator("FutureNullRay"), Rel(
            Rel(D(0), Lt, App(k, D(0))), Land, Equal(Apply("minkowski", k, k), D(0))));
    }

    private static Formula FrameFormula()
    {
        Formula r = F.Id("r");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula screen = Apply("screenFrame", r, a);
        Formula transverse = All("a", Apply("Fin", D(2)),
            Equal(Apply("minkowski", screen, Apply("nullGenerator", r)), D(0)));
        Formula orthonormal = All("a", Apply("Fin", D(2)), All("b", Apply("Fin", D(2)),
            Equal(Apply("minkowski", screen, Apply("screenFrame", r, b)), Apply("delta", a, b))));
        return All("r", Operator("FutureNullRay"), Rel(Parens(transverse), Land, Parens(orthonormal)));
    }

    private static Formula Field(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula Parens(Formula formula) => Seq(Open, formula, Close);
    private static Formula RayFamily(Formula count) => Arrow(Apply("Fin", count), Operator("FutureNullRay"));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Dimension(Formula type) => Apply("finrank", Field("R"), type);
    private static Formula Operator(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Apply(string name, params Formula[] args) => new Formula.Apply(Operator(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula left, Formula relation, Formula right) =>
        Seq(Open, left, Sp, relation, Sp, right, Close);
}
