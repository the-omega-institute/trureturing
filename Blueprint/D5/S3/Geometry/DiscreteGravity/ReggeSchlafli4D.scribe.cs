using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.DiscreteGravity;

internal sealed class ReggeSchlafli4DDocument : IScribeDocumentDefinition
{
    private static LibraryNoteRef Schlafli => LibraryNoteRef.Create("D5/L/Convexity/rivinschlenker2000schlafli");
    private const string Prefix = "D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Euclidean simplex normals, the Schläfli identity, and variation of the four-dimensional Regge action.",
        H("Simplex normals and Regge variation"),
        Blocks(
            Theorem("minkowski-closure", "minkowski_closure", "Closure of the cofactor normals",
                "Take the edges from vertex zero as rows of the edge matrix E. For each other vertex use the corresponding inverse column multiplied by minus the absolute determinant. The normal at vertex zero is minus the sum of those columns. Their sum over all vertices is zero."),
            Theorem("outward-normals", "outward_normal_orthogonality", "Outward facet normals",
                "The inverse matrix pairs each inverse column with its own edge and annihilates the other edges. For every facet, the pairing with a difference of two facet vertices is zero. The pairing with the displacement from a facet vertex toward its opposite vertex equals minus the absolute determinant and is strictly negative."),
            Theorem("hinge-sine", "gram_normal_hinge_sine_identity", "The hinge Gram determinant",
                "Use the Euclidean norm and take the interior dihedral angle to be the arccosine of the negative dot product of the unit outward normals. For distinct opposite vertices the absolute dot product is strictly less than one. The two normal lengths times the sine of the angle equal the absolute edge determinant times the square root of the hinge Gram determinant. Rebase at a hinge vertex and apply the complementary principal minor relation to the edge Gram matrix."),
            Theorem("facet-volumes", "facet_volume_hinge_sine", "The volume-normalized hinge identity",
                "Divide the normal lengths by the facet factorial and the full determinant by the simplex factorial. This gives a ratio of the simplex dimension to the facet dimension, equal to four thirds in dimension four."),
            Theorem("differential-closure", "normal_closure_schlafli_core", "Differentiating the normal pairing",
                "Unit length near the evaluation point makes each diagonal normal derivative vanish. Weighted closure at the evaluation point kills the full double sum. The derivative of each off-diagonal arccosine is the symmetrized pairing divided by its positive sine. The sum over increasing pairs of this derivative weighted by the two normal weights and the sine is zero."),
            Theorem("euclidean-schlafli", "euclidean_simplex_schlafli", "Euclidean Schläfli identity",
                "The vertices are differentiable at the evaluation point and the edge determinant there is nonzero. Every dihedral angle for a distinct pair has the stated derivative. The hinge area is the square root of its Gram determinant divided by the factorial of its dimension. Multiplying the area-weighted sum by the common determinant and factorial recovers the zero sum from differential closure."),
            Theorem("four-dimensional-schlafli", "regge_schlafli_4d", "The ten triangle hinges",
                "In dimension four the five opposite-vertex labels give ten increasing pairs. Each area is one half of the square root of the two-edge Gram determinant. The sum of triangle areas times the corresponding angle derivatives vanishes."),
            Theorem("palatini-variation", "regge_action_palatini_variation", "Regge action variation",
                "A hinge deficit is two pi minus the sum of its incident simplex angles. The action sums area times deficit over the included hinges. The product rule generates an angle variation. Changing the order of the incidence sum gives a sum of local Schläfli terms over the included incidences, each zero by hypothesis. The derivative is the sum of area derivatives times the original deficits. When boundary hinges are omitted, the local cancellation hypothesis applies to the retained incidences of each simplex."),
            Theorem("cosmological-variation", "regge_action_lambda_variation", "Cosmological volume variation",
                "Subtracting a constant cosmological coefficient times the sum of differentiable simplex volumes adds the negative coefficient times the sum of volume derivatives."),
            Theorem("flat-stationarity", "flat_regge_stationarity", "Stationarity at zero deficit",
                "At a configuration with zero deficit at every included hinge, any differentiable variation satisfying the local angle cancellation has zero action derivative."),
            Theorem("holonomy-derivative", "discrete_bianchi_edge_holonomy", "First-order edge holonomy",
                "Write the generators in one common frame and multiply the exponentials in the chosen list order. Every factor is the identity at zero, so the derivative there is the list sum of the deficit-weighted generators. First-order triviality is equivalent to the vanishing of that sum. A simplicial application requires a geometric transport relation that yields first-order triviality in the common frame."),
            Theorem("spherical-triangle", "spherical_triangle_schlafli_counterexample", "Spherical triangle area variation",
                "At parameters between pi over three and pi, the equal-distance unit vertices have three angles equal to the parameter. Each angle derivative is one. The area function in the identity is three times the parameter minus pi. Girard's theorem identifies this spherical excess with the intrinsic area of the triangle. The sum of angle derivatives equals the nonzero derivative of spherical excess, with unit weights at the vertices.")),
        []));

    private static DocumentBlock Theorem(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(FormulaFor(name))),
            name is "euclidean_simplex_schlafli" or "regge_schlafli_4d" or "spherical_triangle_schlafli_counterexample"
                ? AssessedProvenance.FromRepo(Schlafli) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),
            DescribeRole.Theorem);

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), InMacro, Sp, type, Comma, Sp, body);

    private static Formula Fn(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(name)), Open,
            Seq(args.SelectMany((arg, i) => i == 0 ? new[] { arg } : new[] { Comma, Sp, arg }).ToArray()),
            Close);

    private static Formula Rel(Formula left, Formula relation, Formula right) =>
        Seq(left, Sp, relation, Sp, right);

    private static Formula Both(Formula left, Formula right) =>
        Rel(Seq(Open, left, Close), Land, Seq(Open, right, Close));

    private static Formula SumOver(Formula index, Formula term) =>
        Seq(Sum, Underscore, Grp(index), Sp, term);

    private static Formula TimesOf(params Formula[] factors) =>
        Seq(factors.SelectMany((factor, i) => i == 0 ? new[] { factor } : new[] { Sp, Cdot, Sp, factor }).ToArray());

    private static Formula Negate(Formula arg) => Seq(Minus, arg);
    private static Formula Abs(Formula arg) => Seq(Lvert, Sp, arg, Rvert, Sp);
    private static Formula Inner(Formula x, Formula y) => Seq(Langle, Sp, x, Comma, Sp, y, Rangle, Sp);
    private static Formula Norm(Formula arg) => Seq(Vert, Sp, arg, Vert, Sp);
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Zero => D(0);
    private static Formula One => D(1);
    private static Formula NumDiv(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    private static Formula MatrixFour => Fn("Mat", D(4), D(4), Real);
    private static Formula Index(string name, Formula type) => Rel(F.Id(name), InMacro, type);
    private static Formula Domain(Formula left, Formula right) => Rel(left, To, right);
    private static Formula Nonzero(Formula value) => Rel(value, Neq, Zero);
    private static Formula EqTo(Formula left, Formula right) => Rel(left, Eq, right);
    private static Formula At(Formula f, Formula derivative, Formula point) =>
        Fn("HasDerivAt", f, derivative, point);
    private static Formula Derivative(Formula f, Formula point) => Fn("deriv", f, point);
    private static Formula Slice(string slot, Formula expression) =>
        Seq(Open, F.Id(slot), Mapsto, Sp, expression, Close);

    private static Formula VertexLabels(Formula d) => Fn("Fin", Seq(d, Plus, One));
    private static Formula Vertices(Formula d) => Domain(VertexLabels(d), Seq(Real, Caret, Grp(d)));
    private static Formula EdgeDet(Formula v) => Fn("det", Fn("E", v));
    private static Formula Normal(Formula v, Formula i) => Fn("N", v, i);
    private static Formula Dihedral(Formula v, Formula i, Formula j) => Fn("theta", v, i, j);

    private static Formula FormulaFor(string name) => name switch
    {
        "minkowski_closure" => Closure(),
        "outward_normal_orthogonality" => Outward(),
        "gram_normal_hinge_sine_identity" => Hinge(false),
        "facet_volume_hinge_sine" => Hinge(true),
        "normal_closure_schlafli_core" => DifferentialClosure(),
        "euclidean_simplex_schlafli" => SimplexVariation(false),
        "regge_schlafli_4d" => SimplexVariation(true),
        "regge_action_palatini_variation" => ReggeVariation(false, false),
        "regge_action_lambda_variation" => ReggeVariation(true, false),
        "flat_regge_stationarity" => ReggeVariation(false, true),
        "discrete_bianchi_edge_holonomy" => Holonomy(),
        "spherical_triangle_schlafli_counterexample" => Spherical(),
        _ => throw new ArgumentOutOfRangeException(nameof(name))
    };

    private static Formula Closure()
    {
        Formula d = F.Id("d"), v = F.Id("v"), i = F.Id("i");
        return All("d", Nat, All("v", Vertices(d),
            EqTo(SumOver(Index("i", VertexLabels(d)), Normal(v, i)), Zero)));
    }

    private static Formula Outward()
    {
        Formula d = F.Id("d"), v = F.Id("v"), i = F.Id("i"), j = F.Id("j"), k = F.Id("k");
        Formula labels = VertexLabels(d);
        Formula difference = Seq(Fn("v", j), Minus, Fn("v", i));
        Formula inward = Inner(Normal(v, k), Seq(Fn("v", k), Minus, Fn("v", j)));
        return All("d", Nat, All("v", Vertices(d), All("k", labels,
            Rel(Nonzero(EdgeDet(v)), Implies,
                Both(All("i", labels, All("j", labels, Rel(
                    Both(Rel(i, Neq, k), Rel(j, Neq, k)), Implies,
                    EqTo(Inner(Normal(v, k), difference), Zero)))),
                    All("j", labels, Rel(Rel(j, Neq, k), Implies,
                        Both(EqTo(inward, Negate(Abs(EdgeDet(v)))), Rel(inward, Lt, Zero)))))))));
    }

    private static Formula Hinge(bool volumes)
    {
        Formula n = F.Id("n"), d = Seq(Open, n, Plus, D(2), Close), v = F.Id("v");
        Formula i = F.Id("i"), j = F.Id("j");
        Formula sine = Seq(Sin, Sp, Open, Dihedral(v, i, j), Close);
        Formula statement = volumes
            ? EqTo(TimesOf(Fn("V", v, i), Fn("V", v, j), sine),
                TimesOf(NumDiv(Seq(n, Plus, D(2)), Seq(n, Plus, One)), Fn("Vol", v), Fn("A", v, i, j)))
            : Both(Rel(Abs(Inner(Fn("u", v, i), Fn("u", v, j))), Lt, One),
                EqTo(TimesOf(Norm(Normal(v, i)), Norm(Normal(v, j)), sine),
                    TimesOf(Abs(EdgeDet(v)), Seq(Sqrt, Grp(Fn("hingeGramDet", v, i, j))))));
        Formula labels = VertexLabels(d);
        return All("n", Nat, All("v", Vertices(d), All("i", labels, All("j", labels,
            Rel(Both(Nonzero(EdgeDet(v)), Rel(i, Neq, j)), Implies, statement)))));
    }

    private static Formula DifferentialClosure()
    {
        Formula labels = F.Id("I"), space = F.Id("X"), i = F.Id("i"), j = F.Id("j");
        Formula t = F.Id("t"), s = F.Id("s");
        Formula ui = Fn("u", i, t), uj = Fn("u", j, t);
        Formula vi = Fn("V", i), vj = Fn("V", j);
        Formula dui = Fn("du", i), duj = Fn("du", j);
        Formula angle = Slice("s", Fn("arccos", Negate(Inner(Fn("u", i, s), Fn("u", j, s)))));
        Formula sine = Seq(Sin, Sp, Open, Fn("arccos", Negate(Inner(ui, uj))), Close);
        Formula slope = NumDiv(Seq(Inner(ui, duj), Plus, Inner(uj, dui)), sine);
        Formula strict = Rel(Rel(i, Neq, j), Implies, Rel(Abs(Inner(ui, uj)), Lt, One));
        Formula assumptions = Both(
            All("i", labels, Both(At(Slice("s", Fn("u", i, s)), dui, t),
                Fn("EventuallyAt", t, Slice("s", EqTo(Norm(Fn("u", i, s)), One))))),
            Both(All("i", labels, All("j", labels, strict)),
                EqTo(SumOver(Index("i", labels), TimesOf(vi, ui)), Zero)));
        Formula result = Both(
            EqTo(SumOver(Index("i", labels), SumOver(Index("j", labels), TimesOf(vi, vj, Inner(ui, duj)))), Zero),
            Both(All("i", labels, All("j", labels, Rel(Rel(i, Neq, j), Implies, At(angle, slope, t)))),
                EqTo(SumOver(Rel(i, Lt, j), TimesOf(vi, vj, sine, Derivative(angle, t))), Zero)));
        return All("I", Fn("FiniteLinearOrder"), All("X", Fn("RealInnerProductSpace"),
            All("u", Domain(labels, Domain(Real, space)), All("du", Domain(labels, space),
                All("V", Domain(labels, Real), All("t", Real, Rel(assumptions, Implies, result)))))));
    }

    private static Formula SimplexVariation(bool four)
    {
        Formula d = four ? D(4) : Seq(Open, F.Id("n"), Plus, D(2), Close);
        Formula labels = VertexLabels(d), v = F.Id("v"), i = F.Id("i"), j = F.Id("j");
        Formula t = F.Id("t"), s = F.Id("s");
        Formula angle = Slice("s", Dihedral(Fn("v", s), i, j));
        Formula derivative = Derivative(angle, t);
        Formula area = four ? NumDiv(Seq(Sqrt, Grp(Fn("hingeGramDet", Fn("v", t), i, j))), D(2))
            : Fn("A", Fn("v", t), i, j);
        Formula result = EqTo(SumOver(Rel(i, Lt, j), TimesOf(area, derivative)), Zero);
        if (!four)
            result = Both(All("i", labels, All("j", labels,
                Rel(Rel(i, Neq, j), Implies, At(angle, derivative, t)))), result);
        Formula body = All("v", Domain(Real, Vertices(d)), All("t", Real,
            Rel(Both(Nonzero(EdgeDet(Fn("v", t))), All("i", labels,
                Fn("DifferentiableAt", Slice("s", Fn("v", s, i)), t))), Implies, result)));
        return four ? body : All("n", Nat, body);
    }

    private static Formula ReggeVariation(bool cosmological, bool flat)
    {
        Formula hinges = F.Id("H"), cells = F.Id("C"), c = F.Id("K"), h = F.Id("h"), q = F.Id("q");
        Formula s = F.Id("s"), t = F.Id("t"), lambda = F.Id("L");
        Formula deficit = Fn("epsilon", c, F.Id("theta"), h, t);
        Formula hDerivative = At(Slice("s", Fn("A", h, s)), Fn("dA", h), t);
        Formula angleDerivative = At(Slice("s", Fn("theta", h, q, s)), Fn("dtheta", h, q), t);
        Formula volDerivative = At(Slice("s", Fn("Vol", q, s)), Fn("dVol", q), t);
        Formula incidence = Fn("Inc", c, h, q);
        Formula local = EqTo(SumOver(Seq(Index("h", hinges), Comma, Sp, incidence),
            TimesOf(Fn("A", h, t), Fn("dtheta", h, q))), Zero);
        Formula premises = Both(All("h", hinges, hDerivative), All("q", cells,
            Both(All("h", hinges, Rel(incidence, Implies, angleDerivative)), local)));
        if (flat)
            premises = Both(premises, All("h", hinges, EqTo(deficit, Zero)));
        if (cosmological)
            premises = Both(premises, All("q", cells, volDerivative));
        Formula slope = flat ? Zero : SumOver(Index("h", hinges), TimesOf(Fn("dA", h), deficit));
        Formula action = Fn("S", c, F.Id("A"), F.Id("theta"));
        if (cosmological)
        {
            slope = Seq(slope, Minus, TimesOf(lambda, SumOver(Index("q", cells), Fn("dVol", q))));
            action = Fn("SLambda", c, F.Id("A"), F.Id("theta"), F.Id("Vol"), lambda);
        }
        Formula body = All("t", Real, Rel(premises, Implies, At(action, slope, t)));
        if (cosmological)
            body = All("Vol", Domain(cells, Domain(Real, Real)),
                All("dVol", Domain(cells, Real), All("L", Real, body)));
        return All("H", Fn("FiniteType"), All("C", Fn("FiniteType"),
            All("K", Fn("ReggeComplex", hinges, cells), All("A", Domain(hinges, Domain(Real, Real)),
                All("theta", Domain(hinges, Domain(cells, Domain(Real, Real))),
                    All("dA", Domain(hinges, Real), All("dtheta", Domain(hinges, Domain(cells, Real)), body)))))));
    }

    private static Formula Holonomy()
    {
        Formula hinges = F.Id("H"), list = F.Id("L"), h = F.Id("h");
        Formula ordered = Fn("edgeHolonomy", list, F.Id("epsilon"), F.Id("B"));
        Formula sum = SumOver(Index("h", list), TimesOf(Fn("epsilon", h), Fn("B", h)));
        return All("H", Fn("Type"), All("L", Fn("List", hinges),
            All("epsilon", Domain(hinges, Real), All("B", Domain(hinges, MatrixFour),
                Both(At(ordered, sum, Zero), Rel(At(ordered, Zero, Zero), Iff, EqTo(sum, Zero)))))));
    }

    private static Formula Spherical()
    {
        Formula labels = Fn("Fin", D(3)), i = F.Id("i"), j = F.Id("j"), k = F.Id("k");
        Formula t = F.Id("t"), s = F.Id("s"), area = F.Id("area");
        Formula angle = Slice("s", Fn("alpha", s, i, j, k));
        Formula cyclicAngle = Slice("s", Fn("alpha", s, i, Seq(i, Plus, One), Seq(i, Plus, D(2))));
        Formula distinct = Both(Rel(i, Neq, j), Both(Rel(i, Neq, k), Rel(j, Neq, k)));
        Formula h = Both(Rel(NumDiv(Pi, D(3)), Lt, t), Rel(t, Lt, Pi));
        return All("t", Real, Rel(h, Implies, Both(
            All("i", labels, EqTo(Norm(Fn("p", t, i)), One)),
            Both(All("i", labels, All("j", labels, All("k", labels,
                Rel(distinct, Implies, At(angle, One, t))))),
                Both(At(area, D(3), t), Both(
                    EqTo(SumOver(Index("i", labels), Derivative(cyclicAngle, t)), Derivative(area, t)),
                    Nonzero(Derivative(area, t))))))));
    }
}
