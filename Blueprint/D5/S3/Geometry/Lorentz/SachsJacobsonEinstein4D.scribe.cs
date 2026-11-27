using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class SachsJacobsonEinstein4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.";
    private static LibraryNoteRef Jacobson => LibraryNoteRef.Create("D5/L/LieTheory/jacobson1995thermodynamics");
    private static LibraryNoteRef Urbantke => LibraryNoteRef.Create("D5/L/LieTheory/urbantke1984plebanski");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Null optical focusing, the local horizon Clausius limit, and the Einstein equation on a connected chart.",
        H("Sachs focusing and the local horizon equation of state"),
        Blocks(
            Paragraph(Text("The twist-free optical equations govern the expansion, the complex trace-free shear and the area radius of a two-dimensional screen. At an equilibrium horizon cross-section the expansion and shear vanish, so the leading area change along a past-directed interval is controlled by Ricci curvature. Comparing it with the heat flux gives the null Einstein equation. The full null cone determines a symmetric tensor up to the metric. Contracted Bianchi and stress-energy conservation fix that remaining coefficient up to a constant.")),
            Node("optical-data", "OpticalData", "Optical fields",
                "The affine parameter is real. Expansion, radius and Ricci contraction are real-valued, while shear and trace-free tidal driving are complex-valued.", DescribeRole.Definition),
            Node("focusing", "focusing", "Focusing coefficient",
                "Half the sum of complex shear norm squared and the full Ricci contraction gives the second-order focusing coefficient.",
                DescribeRole.Definition, BinaryOptical("focusing", Divide(Add(Call("normSq", Call("shear", V("o"), V("t"))), Call("ricciTerm", V("o"), V("t"))), D(2)))),
            Node("solves-on", "SolvesOn", "Sachs optical equations",
                "At every affine parameter t in the specified set, the expansion derivative is −θ²/2−|σ|²−Rkk, the shear derivative is −θσ−Ψ, and the radius derivative is θρ/2. The derivatives are taken for functions globally typed on the real line, so evaluation at the endpoints of a closed interval is meaningful.", DescribeRole.Definition),
            Node("area", "area", "Area from radius",
                "The cross-sectional area is the square of the area radius.",
                DescribeRole.Definition, BinaryOptical("area", Square(Call("radius", V("o"), V("t"))))),
            Node("radius-slope", "radiusSlope", "Optical radius slope",
                "The affine radius slope is expansion times radius divided by two.",
                DescribeRole.Definition, BinaryOptical("radiusSlope", Divide(Multiply(Call("expansion", V("o"), V("t")), Call("radius", V("o"), V("t"))), D(2)))),
            Node("area-derivative", "hasDerivAt_area", "Area derivative",
                "At each parameter of a solution, the area derivative equals expansion times area by the derivative of a square.", DescribeRole.Theorem),
            Node("radius-slope-derivative", "hasDerivAt_radiusSlope", "Linearized Sachs equation",
                "At each parameter of a solution the derivative of the radius slope equals minus the focusing coefficient times radius. The product rule and expansion equation cancel the terms quadratic in expansion.", DescribeRole.Theorem),
            Node("radius-focusing", "area_radius_focusing", "Second-order focusing on an open set",
                "The actual derivative of the radius agrees locally with the explicit optical radius slope. Therefore the second derivative plus the focusing coefficient times radius vanishes at each parameter of an open solution set.",
                DescribeRole.Theorem, FocusingEquation()),
            Node("nec-bounds", "optical_nec_bounds", "Null energy condition and concavity",
                "On a convex solution set with nonnegative Ricci contraction and radius, the focusing coefficient is nonnegative, the radius slope derivative is nonpositive, and the expansion derivative is at most −θ²/2. Derivative comparison gives antitonicity of the expansion and radius slope, and concavity of the radius.", DescribeRole.Theorem),
            Node("reciprocal-expansion", "reciprocal_expansion_bound", "Inverse expansion estimate",
                "On a closed interval from zero to t with t nonnegative, an initially negative expansion under nonnegative Ricci contraction stays negative. Differentiating its inverse gives a lower derivative bound of one half. Thus its final inverse is at least its initial inverse plus t/2.", DescribeRole.Theorem),
            Node("finite-affine-bound", "no_positive_optics_through_focal_bound", "Finite-affine focusing bound",
                "A regular optical solution throughout the half-open interval from zero to L with initially negative expansion and nonnegative Ricci contraction satisfies L ≤ 2/|θ(0)|. If that endpoint lay strictly inside the solution interval, the inverse expansion estimate would force a nonnegative inverse of a negative expansion.", DescribeRole.Theorem),
            Node("continued-radius-zero", "radius_zero_le_focal_bound", "A continued radius reaches zero",
                "For negative initial expansion and positive initial radius, suppose the radius is continuous through the focal bound, and the optical equations and nonnegative Ricci contraction hold at every positive-radius point. A zero occurs at some strictly positive parameter no greater than the focal bound. In the absence of such a zero, continuity and the intermediate value theorem force the radius to remain positive throughout. The inverse expansion contradiction then occurs at the focal bound itself.", DescribeRole.Theorem),
            Node("tangent-delay", "tangentDelay", "Tangent radius deficit",
                "The radius at zero plus t times its initial optical slope minus the radius at t defines the tangent deficit.",
                DescribeRole.Definition, BinaryOptical("tangentDelay", Subtract(Add(Call("radius", V("o"), D(0)), Multiply(V("t"), Call("radiusSlope", V("o"), D(0)))), Call("radius", V("o"), V("t"))))),
            Node("tangent-delay-nonnegative", "tangent_delay_nonneg", "Nonnegative focusing delay",
                "With nonnegative radius and Ricci contraction on the closed interval from zero to t, the tangent deficit starts at zero and has nonnegative derivative. Hence the final tangent deficit is nonnegative.", DescribeRole.Theorem),
            Node("weyl-generates-shear", "weyl_generates_shear", "Weyl-driven shear",
                "At a solution point with zero shear and nonzero tidal input, the shear derivative is minus the tide and is nonzero. The difference quotient stays nonzero sufficiently near the point in the deleted neighborhood. The shear there is consequently nonzero, and wherever the solution has positive radius and nonnegative Ricci contraction the radius slope has strictly negative derivative. This applies in vacuum.", DescribeRole.Theorem),
            Node("clock-deficit", "clock_deficit_of_optics", "Optical delay in the clock-area bound",
                "For a nonempty finite family of generator samples with positive weights, positive radius throughout each closed past-to-sample interval from zero, nonnegative Ricci contraction and cutoff ε below one, use the radius as the corner density and its tangent deficit as the clock delay. The resulting clock is at least (1−ε) times the square root of weighted area divided by total weight. Equality holds exactly when all sampled delays vanish and all sampled radii agree.", DescribeRole.Theorem),
            Node("tensor-evaluation", "evalMat", "Bilinear tensor evaluation",
                "Contract both vector arguments against the covariant four-by-four matrix entries by a double finite sum.", DescribeRole.Definition),
            Node("screen-trace-and-tide", "screen_trace_and_tide", "Ricci trace and complex Weyl source",
                "Scale the chart generator by a and the chart tidal matrix by a². Its trace equals the Ricci contraction on the scaled generator. Subtraction of half this contraction from each diagonal entry leaves the scaled Weyl tide. The squared scale times the complex Weyl tide is twice the first diagonal component plus twice i times the first off-diagonal component of that scaled Weyl matrix.", DescribeRole.Theorem, notes: [Urbantke]),
            Node("screen-riccati", "screen_riccati_components", "Twist-free screen Riccati components",
                "Write the optical matrix with diagonal entries θ/2+s and θ/2−s and off-diagonal entries u. If the derivative matrix equals minus the matrix square minus a tidal matrix P of trace Rkk, adding the two diagonal equations gives θ′=−θ²/2−2(s²+u²)−Rkk. Subtracting them and using the off-diagonal equation gives the complex shear equation for σ=√2(s+iu), with source √2(P₀₀−Rkk/2+iP₀₁).", DescribeRole.Theorem),
            Node("area-change", "areaChange", "Past horizon area variation",
                "For affine width e, the area at zero minus the area at −e defines the horizon area change.",
                DescribeRole.Definition, All("o", Operator("OpticalData"), All("e", Reals,
                    Equal(Call("areaChange", V("o"), V("e")), Subtract(Call("area", V("o"), D(0)), Call("area", V("o"), Negative(V("e")))))))),
            Node("heat", "heat", "Weighted past horizon heat flux",
                "For real surface gravity κ and heat flux density T, integrate −t T(t) A(t) from −e to zero and multiply by κ.", DescribeRole.Definition),
            Node("first-variation", "horizon_first_variation", "Normalized area and heat limits",
                "Take a solution on a past segment of positive width, with zero expansion and shear at zero, positive initial radius and continuous heat flux on the segment. Normalize both variations by A(0)e²/2. As e decreases to zero through positive values, these ratios tend respectively to Rkk(0) and κ T(0). The divided slope of the expansion is continuous at zero and has value −Rkk(0). The fundamental theorem of calculus rewrites the area change as the same weighted integral used for the heat flux. Bounds on the continuous integrand near zero yield the two limits since the integral of −t is e²/2.", DescribeRole.Theorem, notes: [Jacobson]),
            Node("clausius-null-identity", "null_identity_of_clausius", "Clausius implies the null Einstein equation",
                "Under the same horizon assumptions and with positive κ, ℏ and entropy density η, suppose every positive sufficiently short segment satisfies heat = ℏκη/(2π) times area change. Normalize by the positive area-width factor and use the two limits. Cancelling κ gives Rkk(0)−2πT(0)/(ℏη)=0.", DescribeRole.Theorem, notes: [Jacobson]),
            Node("null-rigidity", "symmetric_eq_metric_of_null", "Metric proportionality from null vanishing",
                "For symmetric real four-by-four matrices S and g, suppose an invertible real linear frame pulls the quadratic form of g back to the Lorentzian form with signature (−+++). If the quadratic form of S vanishes on every null vector of g, transport it through the frame and the time-space splitting to apply Minkowski null-cone rigidity. The certificate uses signature (+−−−), so its coefficient changes sign. Polarization on pairs of coordinate vectors then yields S=f g for a real f.", DescribeRole.Theorem),
            Node("tensor-field", "TensorField", "Covariant tensor fields",
                "A covariant tensor field assigns a real four-by-four matrix to each vector in real four-dimensional coordinate space.", DescribeRole.Definition),
            Node("coordinate-derivative", "coordinateDerivative", "Coordinate partial derivative",
                "Evaluate the real Fréchet derivative of the scalar field on the specified coordinate unit vector.", DescribeRole.Definition),
            Node("tensor-divergence", "tensorDivergence", "Covariant divergence",
                "For inverse metric entries g^{ma} and connection coefficients Γ^d_ma, the b component is the sum over m and a of g^{ma} times the partial derivative of S_ab in direction m minus the connection sums Γ^d_ma S_db and Γ^d_mb S_ad.", DescribeRole.Definition),
            Node("metric-trace", "metricTrace", "Metric trace",
                "The trace is the double sum of g^{ma} S_am over coordinate indices m and a.", DescribeRole.Definition),
            Node("component-differentiability", "ComponentDiff", "Differentiability on a chart",
                "Each of the sixteen real-valued tensor entries is differentiable on the specified set.", DescribeRole.Definition),
            Node("jacobson-einstein", "jacobson_einstein_on", "Einstein equation with constant cosmological term",
                "On an open preconnected chart take differentiable component fields g, its inverse, Ricci R and stress T, with symmetric g, R and T, a pointwise Lorentz frame, and a metric-compatible connection. At each point and nonzero null vector require an equilibrium past optical pencil of positive width and positive surface gravity with continuous heat flux, positive initial radius, initial Ricci and flux values equal to the contractions of R and T, and the Clausius identity on every short segment. Assume the contracted Bianchi identity and vanishing stress divergence. The null Clausius identity and metric proportionality give R−cT=f g for c=2π/(ℏη), with f equal to the metric trace of R−cT divided by four. Metric compatibility and the product rule give div(f g)=df. Bianchi and conservation imply d(f−Rscal/2)=0. The open preconnected chart makes this difference constant, yielding R−(Rscal/2)g+Λg=8πGT for a single real Λ and G=1/(4ℏη).", DescribeRole.Theorem, notes: [Jacobson, Urbantke])),
        []));

    private static DocumentBlock Node(string id, string name, string title, string prose,
        DescribeRole role, Formula? formula = null, LibraryNoteRef[]? notes = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
        formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(notes ?? []), Blocks(Paragraph(Text(prose))), role);

    private static Formula FocusingEquation()
    {
        Formula o = V("o"), i = V("J"), t = V("t");
        Formula hypotheses = Rel(Call("SolvesOn", o, i), Land,
            Rel(Call("IsOpen", i), Land, Rel(t, InMacro, i)));
        Formula r = Call("radius", o);
        Formula equation = Equal(Add(Call("deriv", Call("deriv", r), t),
            Multiply(Call("focusing", o, t), Call("radius", o, t))), D(0));
        return All("o", Operator("OpticalData"),
            All("J", Call("Set", Reals), All("t", Reals, Rel(hypotheses, Implies, equation))));
    }

    private static Formula BinaryOptical(string name, Formula value) =>
        All("o", Operator("OpticalData"), All("t", Reals, Equal(Call(name, V("o"), V("t")), value)));
    private static Formula V(string name) => F.Id(name);
    private static Formula Reals => Seq(Mathbb, Grp(V("R")));
    private static Formula Operator(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Operator(name), [.. args]);
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula Divide(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Negative(Formula a) => new Formula.Negate(a);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula l, Formula op, Formula r) => Seq(Open, l, Sp, op, Sp, r, Close);
}
