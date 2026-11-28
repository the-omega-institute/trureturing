using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class CausalOrderWeylDeformation4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/QuadraticForms/gibbonssolodukhin2007causaldiamonds");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Null-cone rigidity and pointwise reconstruction of four-dimensional Lorentzian curvature.",
        H("Alexandrov volume and null-screen curvature"),
        Blocks(
            Paragraph(Text("In signature (−+++), the quadratic null cone determines a symmetric form up to scale. "
                + "At second order in the proper time, the relative diamond volume reads the Ricci sector. "
                + "The transverse trace-free tides on five distinct light rays supply the Weyl sector.")),
            Node("conformal_metric_same_null_cone_iff", "Null-cone rigidity over a characteristic-zero field",
                "Let K be any field of characteristic zero and let g be symmetric. Write eta for the diagonal matrix "
                + "with entries (−1,1,1,1). The implication tests every vector k in K⁴. Write q(A,k) for kᵀAk. "
                + "The six null directions with time coordinate one and a single spatial entry ±1 fix the time-space "
                + "entries and all spatial diagonal entries. The three directions with time coordinate five and spatial "
                + "entries three and four fix the remaining entries. Degenerate g, including the zero form, is allowed.",
                ConeFormula()),
            Node("null_cone_perturbation_trace_free_split", "Trace-free light-cone variation",
                "For every symmetric perturbation h over the same field, let H be h minus tr_eta(h) eta/4. "
                + "Then tr_eta(H) vanishes. For every eta-null k, the quadratic readings of h and H agree. "
                + "All the readings vanish if and only if H is zero. The conformal line accounts for one of the ten "
                + "symmetric matrix coordinates.",
                SplitFormula()),
            Node("alexandrov_diamond_flat_volume", "Exact flat four-volume",
                "For real proper time tau at least zero, put r(t) = tau/2 − |t|. The cross section at time t has "
                + "Euclidean three-ball volume 4 pi r(t)³/3. Splitting the interval at zero gives two equal integrals.",
                Equal(Slice(Mul(Ratio(Mul(D(4), Pi), D(3)), Pow(Radius, D(3)))), Volume), true),
            Node("alexandrov_diamond_quadratic_moments", "Time and per-coordinate spatial moments",
                "For real proper time tau at least zero, reflection eliminates mixed moments. Each spatial coordinate "
                + "has the same second moment in the three-ball. Integrating the angular mean of x_i² gives "
                + "4 pi r(t)⁵/15. The time and per-coordinate spatial moments are respectively tau²/60 and tau²/30 "
                + "times the flat four-volume.",
                MomentsFormula()),
            Node("alexandrov_diamond_bulk_ricci", "The quadratic density on the fixed domain",
                "For any real matrix A and real tau at least zero, let M_t be the time moment and M_x the "
                + "per-coordinate spatial moment given by the preceding integrals. The bulk density contribution "
                + "uses A_00 M_t plus (A_11 + A_22 + A_33) M_x, all multiplied by −1/6.",
                BulkFormula()),
            Node("alexandrov_diamond_boundary_radius", "The radial displacement in midpoint normal coordinates",
                "Take real tau, r, E and v with r positive. In the truncated null equation, E is the curvature "
                + "reading on the spatial direction and the time leg. The trial displacement is epsilon times v. "
                + "The equation has zero first-order residual exactly at the displayed radial velocity.",
                BoundaryRadiusFormula()),
            Node("alexandrov_diamond_boundary_volume", "First variation of the moving boundary",
                "For real tau at least zero, let E be the three diagonal spatial sectional readings. The angular "
                + "mean of n_i n_j is delta_ij/3, so the three axis values give the angular mean at degree two. "
                + "The volume derivative at epsilon zero uses the cubic radial variation and the flat volume.",
                BoundaryVolumeFormula()),
            Node("alexandrov_diamond_rnc_volume_coefficient", "The bulk and boundary coefficient",
                "For an algebraic curvature tensor R and real tau at least zero, take E_i = R_0i0i in the moving "
                + "boundary model, and A = Ric(R) in the fixed-domain density. Add the moving-boundary volume to "
                + "epsilon times the bulk contribution. At epsilon zero its derivative is the flat volume times "
                + "tau² times D(R,e_0). Here D is the signed relative volume correction and e_0 = (1,0,0,0). "
                + "This model retains the quadratic normal-coordinate density and first-order radial displacement. "
                + "The spatial moments and spherical means supply the cross-section reductions for these interval integrals. "
                + "The smooth spacetime interpretation uses the small-diamond expansion and its remainder estimates.",
                App("HasDerivAtZero", App("truncatedRNCVolume", F.Id("R"), Tau),
                    Mul(Mul(Volume, Pow(Tau, D(2))), Deficit(F.Id("R"), Sub(F.Id("e"), D(0)))))),
            Node("alexandrovO2Deficit", "Directional coefficient",
                "Define D on algebraic curvature and all real directions. For unit timelike u the coefficient "
                + "multiplies squared proper time in the relative volume change. Scalar curvature uses the "
                + "Minkowski trace of Ricci curvature.",
                CoefficientFormula(), true, DescribeRole.Definition),
            Node("alexandrov_o2_weyl_blind", "Every Weyl tensor has zero volume coefficient",
                "For every W in the algebraic Weyl space and every real direction u, the Ricci contraction "
                + "and its trace vanish.",
                Equal(Deficit(F.Id("W"), F.Id("u")), D(0))),
            Node("alexandrov_o2_reconstructs_ricci_iff", "Unit timelike readings separate the Ricci sector",
                "For every algebraic curvature tensor R, vanishing in all unit timelike directions is equivalent "
                + "to the simultaneous vanishing of trace-free Ricci and scalar curvature. The proof tests the "
                + "rest direction, six axial boosts and three directions with two nonzero spatial entries. "
                + "These evaluations recover the quadratic form Ric(R) + Scal(R) eta/6. Its trace recovers Scal(R).",
                Rel(VolumeZero(F.Id("R")), Iff,
                    Rel(Equal(App("ricciPart", F.Id("R")), D(0)), Land,
                        Equal(App("scalarPart", F.Id("R")), D(0))))),
            Node("complete_curvature_reconstruction_volume_and_five_rays", "Joint reconstruction of all twenty components",
                "For every algebraic curvature tensor R and every family r of five distinct future null rays, "
                + "the joint kernel is zero. Volume detects the Ricci sector. Equal Ricci shifts on the two screen "
                + "diagonal entries cancel in the complex tide. Quartic interpolation on the five rays detects the "
                + "remaining Weyl component. For at most four rays, the Weyl quartic vanishing construction gives a "
                + "nonzero curvature with zero tide at every sampled ray and zero volume reading in every direction. "
                + "The observations are specified pointwise on the tangent space. Applying the result to a discrete "
                + "causal order requires a separate rule for obtaining the tidal observations from its comparisons.",
                Rel(Rel(VolumeZero(F.Id("R")), Land, TideZero(F.Id("R"), D(5))), Iff, Equal(F.Id("R"), D(0)))),
            Node("volume_blind_nonzero_weyl_witness", "A polarized Ricci-flat wave",
                "The Weyl tensor W has electric block diag(1,−1,0) and magnetic entries M_01 = M_10 = 1, "
                + "with all other magnetic entries zero. Its volume coefficient vanishes in every real direction "
                + "and its complex screen tide at the finite ray with coordinate one is nonzero.",
                Rel(Rel(F.Id("W"), Neq, D(0)), Land,
                    Rel(All("u", Vector(Field("R")), Equal(Deficit(F.Id("W"), F.Id("u")), D(0))), Land,
                        Rel(App("complexTide", F.Id("W"), App("some", D(1))), Neq, D(0))))),
            Node("screen_blind_nonzero_ricci_witness", "Scalar curvature invisible to every screen",
                "The tensor R_s has scalar curvature one and zero Weyl and trace-free Ricci parts. It is nonzero, "
                + "has zero complex tide on every future null ray, and has a signed volume coefficient −1/72 "
                + "in the rest direction.",
                Rel(Rel(Sub(F.Id("R"), F.Id("s")), Neq, D(0)), Land,
                    Rel(Equal(App("weylPart", Sub(F.Id("R"), F.Id("s"))), D(0)), Land,
                        Rel(All("r", Op("FutureNullRay"),
                                Equal(App("complexTide", Sub(F.Id("R"), F.Id("s")), F.Id("r")), D(0))), Land,
                            Equal(Deficit(Sub(F.Id("R"), F.Id("s")), Sub(F.Id("e"), D(0))), MinusOf(Ratio(D(1), D(7, 2)))))))),
            Node("rest_volume_and_five_tides_surjective", "Independent prescription of volume and tides",
                "For every family r of five distinct future null rays, every real v and every function T from "
                + "Fin 5 to the complex numbers, there is an algebraic curvature tensor with zero trace-free Ricci "
                + "part, rest-frame volume coefficient v, and complex tides T. Interpolate the five values "
                + "in the Weyl sector and scale the scalar tensor by −72v to set the volume value.",
                PrescriptionFormula())),
        []));

    private static DocumentBlock Node(string name, string title, string prose, Formula formula,
        bool literature = false, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula ConeFormula()
    {
        Formula k = F.Id("k");
        Formula g = F.Id("g");
        Formula reads = All("k", Vector(F.Id("K")),
            Rel(Equal(App("q", Op("eta"), k), D(0)), Implies, Equal(App("q", g, k), D(0))));
        return Rel(reads, Iff, Seq(Exists, Sp, Omega, Colon, Sp, F.Id("K"), Comma, Sp,
            Equal(g, Mul(Omega, Op("eta")))));
    }

    private static Formula SplitFormula()
    {
        Formula h = F.Id("h");
        Formula Hf = F.Id("H");
        Formula k = F.Id("k");
        Formula reads = All("k", Vector(F.Id("K")), Rel(Equal(App("q", Op("eta"), k), D(0)), Implies,
            Equal(App("q", h, k), App("q", Hf, k))));
        Formula kernel = All("k", Vector(F.Id("K")), Rel(Equal(App("q", Op("eta"), k), D(0)), Implies,
            Equal(App("q", h, k), D(0))));
        return Rel(Equal(h, Rel(Mul(Ratio(TraceEta(h), D(4)), Op("eta")), Plus, Hf)), Land,
            Rel(Equal(TraceEta(Hf), D(0)), Land, Rel(reads, Land, Rel(kernel, Iff, Equal(Hf, D(0))))));
    }

    private static Formula MomentsFormula()
    {
        Formula time = Slice(Mul(Pow(F.Id("t"), D(2)), Mul(Ratio(Mul(D(4), Pi), D(3)), Pow(Radius, D(3)))));
        Formula space = Slice(Mul(Ratio(Mul(D(4), Pi), D(1, 5)), Pow(Radius, D(5))));
        return Rel(Equal(time, Mul(Ratio(Pow(Tau, D(2)), D(6, 0)), Volume)), Land,
            Equal(space, Mul(Ratio(Pow(Tau, D(2)), D(3, 0)), Volume)));
    }

    private static Formula BulkFormula()
    {
        Formula a = F.Id("A");
        Formula sum = Rel(Mul(Sub(a, D(0, 0)), Sub(F.Id("M"), F.Id("t"))), Plus,
            Mul(Rel(Rel(Sub(a, D(1, 1)), Plus, Sub(a, D(2, 2))), Plus, Sub(a, D(3, 3))),
                Sub(F.Id("M"), F.Id("x"))));
        Formula coeff = Rel(MinusOf(Ratio(Sub(a, D(0, 0)), D(1, 2, 0))), Minus,
            Ratio(TraceEta(a), D(1, 8, 0)));
        return Equal(Mul(MinusOf(Ratio(D(1), D(6))), sum), Mul(Mul(Volume, Pow(Tau, D(2))), coeff));
    }

    private static Formula BoundaryRadiusFormula()
    {
        Formula r = F.Id("r");
        Formula v = F.Id("v");
        Formula term = Rel(r, Plus, Mul(Varepsilon, v));
        Formula scale = Rel(D(1), Minus, Mul(Varepsilon, Ratio(Mul(Pow(Tau, D(2)), F.Id("E")), D(1, 2))));
        return Rel(App("HasDerivAtZero", Rel(Mul(Pow(term, D(2)), scale), Minus, Pow(r, D(2))), D(0)), Iff,
            Equal(v, Ratio(Mul(Mul(Pow(Tau, D(2)), F.Id("E")), r), D(2, 4))));
    }

    private static Formula BoundaryVolumeFormula()
    {
        Formula sum = Seq(Sum, Underscore, Grp(F.Id("i")), Sp, Sub(F.Id("E"), F.Id("i")));
        Formula rad = Mul(Radius, Rel(D(1), Plus,
            Mul(Varepsilon, Ratio(Mul(Pow(Tau, D(2)), Sub(F.Id("E"), F.Id("i"))), D(2, 4)))));
        Formula volume = Slice(Seq(Sum, Underscore, Grp(F.Id("i")), Sp,
            Mul(Ratio(Mul(D(4), Pi), D(9)), Pow(rad, D(3)))));
        return App("HasDerivAtZero", volume, Ratio(Mul(Mul(Volume, Pow(Tau, D(2))), sum), D(2, 4)));
    }

    private static Formula CoefficientFormula()
    {
        Formula r = F.Id("R");
        Formula u = F.Id("u");
        return Equal(Deficit(r, u), Rel(Ratio(App("Ric", r, u, u), D(3, 0)), Plus,
            Ratio(Mul(App("Scal", r), App("minkowski", u, u)), D(1, 8, 0))));
    }

    private static Formula PrescriptionFormula()
    {
        Formula r = F.Id("R");
        Formula t = F.Id("T");
        Formula readings = All("i", App("Fin", D(5)), Equal(
            App("complexTide", r, App("r", F.Id("i"))), new Formula.Apply(t, [F.Id("i")])));
        return Seq(Exists, Sp, r, Comma, Sp, Rel(Equal(App("ricciPart", r), D(0)), Land,
            Rel(Equal(Deficit(r, Sub(F.Id("e"), D(0))), F.Id("v")), Land, readings)));
    }

    private static Formula VolumeZero(Formula r) => All("u", Vector(Field("R")), Rel(
        Equal(App("minkowski", F.Id("u"), F.Id("u")), MinusOf(D(1))), Implies, Equal(Deficit(r, F.Id("u")), D(0))));
    private static Formula TideZero(Formula curvature, Formula n) => All("i", App("Fin", n),
        Equal(App("complexTide", curvature, App("r", F.Id("i"))), D(0)));
    private static Formula Deficit(Formula r, Formula u) => new Formula.Apply(F.Id("D"), [r, u]);
    private static Formula Volume => Mul(Ratio(Pi, D(2, 4)), Pow(Tau, D(4)));
    private static Formula Radius => Rel(Ratio(Tau, D(2)), Minus, Seq(Bar, F.Id("t"), Bar));
    private static Formula Slice(Formula integrand) => Seq(Int,
        Underscore, Grp(MinusOf(Ratio(Tau, D(2)))), Caret, Grp(Ratio(Tau, D(2))), Sp, integrand, Thin, F.Id("dt"));
    private static Formula TraceEta(Formula a) =>
        new Formula.Apply(Sub(Op("tr"), F.Id("eta")), [a]);
    private static Formula Field(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula Vector(Formula field) => Pow(field, D(4));
    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula App(string name, params Formula[] args) => new Formula.Apply(Op(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Open, new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body), Close);
    private static Formula Equal(Formula a, Formula b) => Rel(a, Eq, b);
    private static Formula Rel(Formula a, Formula op, Formula b) => Seq(Open, a, Sp, op, Sp, b, Close);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Thin, b);
    private static Formula Ratio(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula MinusOf(Formula a) => Seq(Minus, a);
    private static Formula Pow(Formula a, Formula b) => Seq(Grp(a), Caret, Grp(b));
    private static Formula Sub(Formula a, Formula b) => Seq(Grp(a), Underscore, Grp(b));
}
