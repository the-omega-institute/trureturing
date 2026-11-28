using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class HorizonThermodynamicsJacobson4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/HorizonThermodynamicsJacobson4D.";
    private static Formula R => NumberField("R");
    private static Formula C => NumberField("C");
    private static Formula Chart => Seq(R, Caret, Grp(D(4)));
    private static Formula Index => Call("Fin", D(4));
    private static Formula Eta => Op("eta");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Flat-chart horizon thermodynamics and optical focusing in four dimensions.",
        H("Null-cone closure and horizon focusing"),
        Blocks(
            Result("null-cone", "symmetric_null_vanishing_iff_smul_eta", "Null-cone rigidity",
                "Use the metric η = diag(−1,1,1,1). The two null rays in each time–space plane "
                + "give equal spatial diagonal entries and eliminate each time–space entry. "
                + "For each spatial pair, a null vector with time component 5 and spatial components 3 and 4 "
                + "then eliminates the mixed spatial entry. The argument works over every field of characteristic zero.",
                NullCone()),
            Result("bianchi-closure", "jacobson_bianchi_einstein_equation", "One integration constant",
                "On the preconnected open domain U, the coupling is c and the matrix fields R and T are symmetric. Their entries "
                + "are differentiable at each point. Write E = R − trη(R)η/2 and "
                + "p = (R − cT)₀₀. Null-cone rigidity applied to the symmetric residual gives cT − R = pη on U. "
                + "The contracted derivative div uses "
                + "Σₐ ηₐₐ ∂ₐ in the first slot of each matrix field. "
                + "The Bianchi and conservation equations force each coordinate derivative of p + trη(R)/2 to vanish. "
                + "That scalar is locally constant and hence constant on U. This is the flat-chart form of "
                + "the algebraic closure in Jacobson's Thermodynamics of Spacetime (1995), culminating in his Eq. (6).",
                Bianchi()),
            Result("vacuum-indeterminacy", "cosmological_constant_indeterminacy_counterexample",
                "Vacuum cosmological-constant indeterminacy",
                "For the constant Ricci field R(λ) = λη, the trace is 4λ. With T = 0 the null "
                + "contractions and both divergences vanish everywhere and E + λη = 0. "
                + "The 00 entry distinguishes R(λ) from R(μ) for distinct constants.",
                Vacuum()),
            Result("raychaudhuri", "raychaudhuri_monotonic_focusing", "Expansion and shear focusing",
                "At time t, p is the null Ricci flux and s is the complex shear. The squared shear norm "
                + "and the nonnegative Ricci flux both reduce the derivative of the expansion f.",
                Raychaudhuri()),
            Result("caustic", "hawking_penrose_caustic_bound", "Finite affine ceiling",
                "Continuity up to both endpoints and the interior differential inequality make the initially "
                + "negative expansion f nonincreasing. Its reciprocal minus t/2 is nondecreasing. "
                + "The reciprocal stays strictly negative for a finite expansion, which gives a strict endpoint bound. "
                + "The denominator in the pointwise comparison is positive throughout the interval.",
                Caustic()),
            Result("caustic-sharpness", "hawking_penrose_caustic_sharpness", "Sharpness of the ceiling",
                "For every positive pole position T, the function f(t) = −2/(T − t) solves the equality "
                + "throughout t < T and attains the reciprocal comparison with equality. "
                + "Its restriction gives a finite solution on every [0,L] with 0 < L < T.",
                Sharpness()),
            Result("stationary-rigidity", "stationary_horizon_shear_weyl_rigidity", "Stationary optical rigidity",
                "The expansion f vanishes on an open interval, so its derivative there vanishes. "
                + "Nonzero shear would give a strictly negative expansion derivative. With shear zero, Raychaudhuri gives zero Ricci flux p. "
                + "The Sachs equation then forces the Weyl tidal component w driving that shear to vanish on the same interval.",
                Stationary()),
            Result("stationary-qnec", "qfc_iff_qnec_at_stationary_horizon", "Stationary QFC and QNEC",
                "For one affine generator, take area A, expansion f, shear s, flux p, and outside entropy S. "
                + "The first derivative of A is fA near the evaluation parameter t. "
                + "At zero expansion and shear the second derivative of the area is −A(t)p(t). "
                + "With A(t)>0 and G>0, the sign of the second generalized entropy variation gives the "
                + "single-generator stationary bound. The normalized quantum expansion has the same derivative sign "
                + "at this point since A′(t)=0. The Ricci flux is 8πG times the null stress. "
                + "This is the stationary diagonal relation considered by Bousso et al. in Quantum Focusing (2016), §5.2.",
                Quantum()),
            Result("clausius-pinching", "clausius_area_monotonicity_from_record_pinching",
                "Area assigned to basis pinching",
                "For a finite density state ρ let P(ρ) be its diagonal pinching and let A and B be their "
                + "matrices before and after pinching. Assign the area change ΔA = 4G(S(P(ρ)) − S(ρ)). "
                + "The entropy identity gives relative entropy D(ρ∥P(ρ)). Positivity of A implies that a zero "
                + "diagonal entry forces the whole corresponding column to vanish. Therefore the kernel of B "
                + "is contained in the kernel of A. The spectral-ceiling Klein inequality bounds D from below "
                + "by a positive multiple of the squared Hilbert–Schmidt distance. The area change vanishes "
                + "exactly when pinching fixes the matrix, and is positive for any deleted nonzero off-diagonal entry.",
                Pinching())),
        []));

    private static DocumentBlock Result(string id, string name, string title, string prose, Formula formula) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula NullCone()
    {
        var k = F.Id("k");
        var a = F.Id("a");
        var b = F.Id("b");
        var matrix = F.Id("S");
        var nullValue = Summed("a", Mul(At(Eta, a, a), Mul(At(k, a), At(k, a))));
        var quadratic = Summed("a", Summed("b", Mul(At(k, a), Mul(At(matrix, a, b), At(k, b)))));
        return All("K", Op("Type"), Seq(Class("Field", F.Id("K")), Sp, Class("CharZero", F.Id("K")), Sp,
            All("S", Mat(F.Id("K")), If(Equal(Transpose(matrix), matrix),
                Rel(All("k", Pow(F.Id("K"), D(4)), If(Equal(nullValue, D(0)), Equal(quadratic, D(0)))),
                    Iff, Ex("c", F.Id("K"), Equal(matrix, Mul(F.Id("c"), Eta))))))));
    }

    private static Formula Bianchi()
    {
        var u = F.Id("U");
        var x = F.Id("x");
        var k = F.Id("k");
        var r = At(F.Id("R"), x);
        var t = At(F.Id("T"), x);
        var e = At(F.Id("E"), x);
        var coupling = F.Id("c");
        var hypotheses = And(Call("Open", u), Call("Preconnected", u),
            On("x", Chart, u, And(
                Call("DifferentiableEntriesAt", F.Id("R"), x),
                Call("DifferentiableEntriesAt", F.Id("T"), x),
                Equal(Transpose(r), r), Equal(Transpose(t), t),
                All("k", Chart, If(Equal(NullNorm(k), D(0)),
                    Equal(Contract(k, Sub(r, Mul(coupling, t))), D(0)))),
                All("b", Index, And(Equal(Call("div", F.Id("E"), x, F.Id("b")), D(0)),
                    Equal(Call("div", F.Id("T"), x, F.Id("b")), D(0)))))));
        var y = F.Id("y");
        var ricci = At(F.Id("R"), y);
        var traceHalf = Div(Call("MinkowskiTrace", ricci), D(2));
        var residual = Sub(ricci, Mul(coupling, At(F.Id("T"), y)));
        var definitions = All("y", Chart, And(
            Equal(At(F.Id("E"), y), Sub(ricci, Mul(traceHalf, Eta))),
            Equal(At(F.Id("p"), y), At(residual, D(0), D(0)))));
        var scalar = Seq(y, Sp, Mapsto, Sp, Add(At(F.Id("p"), y), traceHalf));
        var derivative = On("x", Chart, u, Call("HasFDerivAt", scalar, D(0), x));
        var equation = Ex("l", R, On("x", Chart, u,
            Equal(Add(e, Mul(F.Id("l"), Eta)), Mul(coupling, t))));
        var body = All("E", Arrow(Chart, Mat(R)), All("p", Arrow(Chart, R),
            If(And(definitions, hypotheses), And(derivative, equation))));
        return All("U", Call("Set", Chart), All("R", Arrow(Chart, Mat(R)),
            All("T", Arrow(Chart, Mat(R)), All("c", R, body))));
    }

    private static Formula Vacuum()
    {
        var x = F.Id("x");
        var l = F.Id("l");
        var k = F.Id("k");
        var b = F.Id("b");
        var coefficient = F.Id("p");
        var ricci = At(F.Id("R"), coefficient, x);
        var corrected = At(F.Id("E"), coefficient, x);
        var tensorFamily = Arrow(R, Arrow(Chart, Mat(R)));
        var definitions = And(All("x", Chart, Equal(At(F.Id("T"), x), D(0))),
            All("p", R, All("x", Chart, And(
                Equal(ricci, Mul(coefficient, Eta)),
                Equal(corrected, Sub(ricci, Mul(Div(Call("MinkowskiTrace", ricci), D(2)), Eta)))))));
        var vacuum = All("p", R, All("x", Chart, And(
            All("k", Chart, If(Equal(NullNorm(k), D(0)),
                Equal(Contract(k, Sub(ricci, Mul(F.Id("c"), At(F.Id("T"), x)))), D(0)))),
            All("b", Index, Equal(Call("div", At(F.Id("E"), coefficient), x, b), D(0))),
            Equal(Add(corrected, Mul(coefficient, Eta)), D(0)))));
        var conserved = All("x", Chart, All("b", Index, Equal(Call("div", F.Id("T"), x, b), D(0))));
        var distinct = Rel(At(F.Id("R"), l), Neq, At(F.Id("R"), F.Id("m")));
        var body = All("R", tensorFamily, All("T", Arrow(Chart, Mat(R)), All("E", tensorFamily,
            If(And(Rel(l, Neq, F.Id("m")), definitions), And(vacuum, conserved, distinct)))));
        return All("c", R, All("l", R, All("m", R, body)));
    }

    private static Formula Raychaudhuri()
    {
        var t = F.Id("t");
        var f = At(F.Id("f"), t);
        var s = At(F.Id("s"), t);
        var p = At(F.Id("p"), t);
        var d = At(Prime(F.Id("f")), t);
        var expansion = Negate(Div(Square(f), D(2)));
        return OpticalVariables(All("t", R, If(And(HasDerivative(F.Id("f"), Ray(f, s, p), t), Rel(D(0), Le, p)),
            And(Rel(d, Le, expansion), Rel(expansion, Le, D(0)),
                If(Rel(s, Neq, D(0)), Rel(d, Lt, expansion))))));
    }

    private static Formula Caustic()
    {
        var t = F.Id("t");
        var f = F.Id("f");
        var ft = At(f, t);
        var fzero = At(f, D(0));
        var l = F.Id("L");
        var closed = Seq(OpenBracket, D(0), Comma, Sp, l, CloseBracket);
        var open = Seq(Open, D(0), Comma, Sp, l, Close);
        return All("f", Arrow(R, R), All("L", R,
            If(And(Rel(D(0), Le, l), Rel(fzero, Lt, D(0)), Call("ContinuousOn", f, closed),
                    Call("DifferentiableOn", f, open),
                    On("t", R, open, Rel(At(Prime(f), t), Le, Negate(Div(Square(ft), D(2)))))),
                And(On("t", R, closed, And(Rel(ft, Lt, D(0)),
                        Rel(Div(t, D(2)), Le, Sub(Div(D(1), ft), Div(D(1), fzero))),
                        Rel(ft, Le, Div(fzero, Add(D(1), Mul(Div(fzero, D(2)), t)))))),
                    Rel(l, Lt, Div(Negate(D(2)), fzero))))));
    }

    private static Formula Sharpness()
    {
        var pole = F.Id("T");
        var t = F.Id("t");
        var f = F.Id("f");
        var fzero = At(f, D(0));
        var ft = At(f, t);
        return All("T", R, If(Rel(D(0), Lt, pole),
            All("f", Arrow(R, R), If(All("t", R, If(Rel(t, Lt, pole), Equal(At(f, t), Div(Negate(D(2)), Sub(pole, t))))),
                And(Rel(fzero, Lt, D(0)), Equal(pole, Div(Negate(D(2)), fzero)),
                    All("t", R, If(Rel(t, Lt, pole), And(
                        HasDerivative(f, Negate(Div(Square(ft), D(2))), t),
                        Equal(Sub(Div(D(1), ft), Div(D(1), fzero)), Div(t, D(2)))))))))));
    }

    private static Formula Stationary()
    {
        var t = F.Id("t");
        var f = At(F.Id("f"), t);
        var s = At(F.Id("s"), t);
        var p = At(F.Id("p"), t);
        var w = At(F.Id("w"), t);
        var interval = Seq(Open, F.Id("a"), Comma, Sp, F.Id("b"), Close);
        return All("a", R, All("b", R, OpticalVariables(All("w", Arrow(R, C),
            If(On("t", R, interval, And(HasDerivative(F.Id("f"), Ray(f, s, p), t),
                HasDerivative(F.Id("s"), Sub(Negate(Mul(Call("ofReal", f), s)), w), t),
                Rel(D(0), Le, p), Equal(f, D(0)))),
                On("t", R, interval, And(Equal(p, D(0)), Equal(s, D(0)), Equal(w, D(0)))))))));
    }

    private static Formula Quantum()
    {
        var g = F.Id("G");
        var t = F.Id("t");
        var u = F.Id("u");
        var area = F.Id("A");
        var a = At(area, t);
        var flux = At(F.Id("p"), t);
        var entropy = F.Id("S");
        var slope = F.Id("H");
        var second = F.Id("h");
        var fourG = Mul(D(4), g);
        var value = Add(Negate(Mul(Div(a, fourG), flux)), second);
        var qfc = Rel(value, Le, D(0));
        var p = Op("pi");
        var x = F.Id("x");
        var gen = Parens(Seq(u, Sp, Mapsto, Sp, Add(Div(At(area, u), fourG), At(entropy, u))));
        var genPrime = Parens(Seq(u, Sp, Mapsto, Sp,
            Add(Div(Mul(At(F.Id("f"), u), At(area, u)), fourG), At(slope, u))));
        var hypotheses = And(Rel(D(0), Lt, g), Rel(D(0), Lt, a),
            Near("u", t, HasDerivative(area, Mul(At(F.Id("f"), u), At(area, u)), u)),
            Near("u", t, HasDerivative(entropy, At(slope, u), u)),
            HasDerivative(slope, second, t),
            HasDerivative(F.Id("f"), Ray(At(F.Id("f"), t), At(F.Id("s"), t), flux), t),
            Equal(At(F.Id("f"), t), D(0)), Equal(At(F.Id("s"), t), D(0)));
        return All("G", R, All("t", R, OpticalVariables(All("A", Arrow(R, R), All("S", Arrow(R, R),
            All("H", Arrow(R, R), All("h", R, If(hypotheses, And(
                Near("u", t, HasDerivative(gen, At(genPrime, u), u)),
                HasDerivative(genPrime, value, t), Rel(qfc, Iff, Rel(Mul(Div(fourG, a), second), Le, flux)),
                All("x", R, If(Equal(flux, Mul(Mul(Mul(D(8), p), g), x)),
                    Rel(qfc, Iff, Rel(Div(second, Mul(Mul(D(2), p), a)), Le, x)))))))))))));
    }

    private static Formula Pinching()
    {
        var n = F.Id("N");
        var g = F.Id("G");
        var rho = F.Id("q");
        var pinched = Call("P", rho);
        var change = Mul(Mul(D(4), g), Sub(Call("S", pinched), Call("S", rho)));
        var a = Call("matrix", rho);
        var b = Call("matrix", pinched);
        var i = F.Id("i");
        var j = F.Id("j");
        return All("N", Op("Type"), Seq(Class("Fintype", n), Sp, Class("DecidableEq", n), Sp,
            All("G", R, All("q", Call("DensityState", n), If(Rel(D(0), Lt, g), And(
                Equal(change, Mul(Mul(D(4), g), Call("D", rho, pinched))), Rel(D(0), Le, change),
                All("i", n, All("j", n, If(And(Rel(i, Neq, j), Rel(At(a, i, j), Neq, D(0))),
                    Rel(D(0), Lt, change)))),
                Rel(Equal(change, D(0)), Iff, Equal(b, a))))))));
    }

    private static Formula OpticalVariables(Formula body) =>
        All("f", Arrow(R, R), All("s", Arrow(R, C), All("p", Arrow(R, R), body)));
    private static Formula Ray(Formula f, Formula s, Formula p) =>
        Sub(Sub(Negate(Div(Square(f), D(2))), Square(Seq(Vert, Sp, s, Sp, Vert))), p);
    private static Formula HasDerivative(Formula f, Formula v, Formula t) => Call("HasDerivAt", f, v, t);
    private static Formula NullNorm(Formula k) => Call("eta", k, k);
    private static Formula Contract(Formula k, Formula s) =>
        Mul(Mul(Transpose(k), s), k);
    private static Formula Summed(string a, Formula value) => Seq(Sum, Underscore, Grp(F.Id(a)), Sp, value);
    private static Formula Near(string name, Formula t, Formula body)
    {
        var radius = F.Id("r");
        var displacement = Seq(Vert, Sp, Sub(F.Id(name), t), Sp, Vert);
        return Ex("r", R, And(Rel(D(0), Lt, radius),
            All(name, R, If(Rel(displacement, Lt, radius), body))));
    }
    private static Formula On(string name, Formula type, Formula set, Formula body) =>
        All(name, type, If(Rel(F.Id(name), InMacro, set), body));
    private static Formula NumberField(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula Mat(Formula k) => At(Seq(Op("Mat"), Underscore, Grp(Seq(D(4), Times, D(4)))), k);
    private static Formula Arrow(Formula a, Formula b) => Rel(a, To, b);
    private static Formula Class(string name, Formula k) => Seq(OpenBracket, Call(name, k), CloseBracket);
    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => At(Op(name), args);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Transpose(Formula value) => Pow(Parens(value), F.Id("T"));
    private static Formula Square(Formula value) => Pow(Parens(value), D(2));
    private static Formula Pow(Formula value, Formula power) => Seq(value, Caret, Grp(power));
    private static Formula Prime(Formula value) => Seq(value, Apos);
    private static Formula Negate(Formula value) => Seq(Minus, Sp, value);
    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Mul(Formula a, Formula b) => Rel(a, Cdot, b);
    private static Formula Add(Formula a, Formula b) => Rel(a, Plus, b);
    private static Formula Sub(Formula a, Formula b) => Rel(a, Minus, b);
    private static Formula If(Formula a, Formula b) => Rel(a, Implies, b);
    private static Formula Parens(Formula value) => Seq(Open, value, Close);
    private static Formula GroupBinder(Formula term) => term is Formula.Bind ? Parens(term) : term;
    private static Formula Rel(Formula a, Formula r, Formula b) =>
        Parens(Seq(GroupBinder(a), Sp, r, Sp, GroupBinder(b)));
    private static Formula And(params Formula[] terms)
    {
        var parts = new List<Formula> { GroupBinder(terms[0]) };
        foreach (var term in terms[1..])
            parts.AddRange([Sp, Land, Sp, GroupBinder(term)]);
        return Parens(Seq([.. parts]));
    }
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
}
