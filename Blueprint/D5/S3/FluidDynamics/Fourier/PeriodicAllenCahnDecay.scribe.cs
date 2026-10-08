using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Fourier;

internal sealed class PeriodicAllenCahnDecayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd real classical profiles on the circle satisfy the Allen-Cahn energy identity and converge in squared L2 energy to zero when diffusion dominates nonnegative linear growth, including equality of the two rates.",
        H("Decay of odd periodic Allen-Cahn profiles"),
        Blocks(
            Node("ScalarRegular", "Scalar regularity", ScalarRegularFormula(),
                "The profile is continuous for nonnegative time, periodic with period 2 Real.pi, and has time, first space and second space derivatives for positive time. All three derivative functions are jointly continuous there. The record imposes no equation or initial data.", DescribeRole.Definition),
            Node("energy", "Squared energy on one period", EnergyFormula(),
                "The measure is volume and the integral is the oriented intervalIntegral from -Real.pi to Real.pi.", DescribeRole.Definition),
            Node("slice_continuousOn", "Continuity of a time slice", SliceFormula(),
                "Continuity on a product restricts to a continuous spatial slice at any time belonging to the time set.", DescribeRole.Lemma),
            Node("energy_zero_of_gronwall", "Zero initial energy stays zero", ZeroFormula(),
                "Continuity at the endpoints and the differential inequality on the open time interval suffice. No derivative at time zero is required.", DescribeRole.Lemma),
            Node("ScalarRegular.slice_continuous", "Continuous spatial slices", RegularSliceFormula(),
                "Every nonnegative time slice of a scalar regular profile is continuous on the whole real line.", DescribeRole.Lemma),
            Node("ScalarRegular.energy_continuous", "Energy is continuous in time", EnergyContinuousFormula(),
                "Joint continuity on nonnegative time and compactness of a spatial period give continuity of the energy including at time zero.", DescribeRole.Lemma),
            Node("energy_nonnegative", "Nonnegative squared energy", NonnegativeFormula(),
                "The increasing interval endpoints make the integral of a square nonnegative, without any regularity assumption on the profile.", DescribeRole.Lemma),
            Node("pde_energy_deriv", "Diffusion and forcing energy identity", PdeEnergyFormula(),
                "For a continuous forcing term at a fixed positive time, periodic integration by parts gives the derivative-square contribution -2*D times its integral; this contribution is nonpositive when D is nonnegative.", DescribeRole.Lemma),
            Node("odd_allen_cahn_decay", "Odd Allen-Cahn evolution decays", DecayFormula(),
                "The odd profile has zero spatial mean. Parseval and the derivative formula for Fourier coefficients give the first-eigenvalue inequality. The energy identity then yields exponential decay for mu < D and a quadratic differential inequality with reciprocal decay for mu = D > 0. The conclusion is a limit for every scalar regular solution satisfying the displayed hypotheses; existence is not asserted.", DescribeRole.Theorem),
            Node("ScalarRegular.sub", "Regularity under subtraction", SubFormula(),
                "Subtracting two scalar regular profiles preserves their regularity and period.", DescribeRole.Lemma),
            Node("ScalarRegular.reflect", "Regularity under reflection", ReflectFormula(),
                "Spatial reflection changes the sign of the first derivative and preserves the second derivative.", DescribeRole.Lemma),
            Node("ScalarRegular.affine", "Regularity under affine combinations", AffineFormula(),
                "Constant affine combinations preserve scalar regularity.", DescribeRole.Lemma),
            Node("affine_derivatives", "Time and second space derivatives of affine combinations", AffineDerivativeFormula(),
                "The constant term has zero derivatives and the two other terms differentiate linearly.", DescribeRole.Lemma))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("periodic-allen-cahn-" + name.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name.Split('.')[^1]), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Regular(Formula w) => Call("ScalarRegular", w);
    private static Formula E(Formula w) => Call("energy", w);
    private static Formula E(Formula w, Formula t) => Call("energy", w, t);
    private static Formula ScalarRegularFormula()
    {
        var w = A("w"); var t = A("t"); var x = A("x");
        var td = Lam("t", R(), Lam("x", R(), Dt(w, t, x)));
        var xd = Lam("t", R(), Lam("x", R(), Dx(w, t, x)));
        var xxd = Lam("t", R(), Lam("x", R(), Dxx(w, t, x)));
        return All("w", W(), Iff(Regular(w), Ands(
            Cont(w, false), NonnegTime(Call("Function.Periodic", Apply(w, t), Period())),
            PosTime(All("x", R(), Call("HasDerivAt", Lam("r", R(), Value(w, A("r"), x)), Dt(w, t, x), t))),
            PosTime(All("x", R(), Call("HasDerivAt", Apply(w, t), Dx(w, t, x), x))),
            PosTime(All("x", R(), Call("HasDerivAt", Call("deriv", Apply(w, t)), Dxx(w, t, x), x))),
            Cont(td, true), Cont(xd, true), Cont(xxd, true))));
    }
    private static Formula EnergyFormula() => All("w", W(), All("t", R(),
        Eq(E(A("w"), A("t")), Interval(Pow(Value(A("w"), A("t"), A("x")), 2)))));
    private static Formula SliceFormula()
    {
        var f = A("F"); var s = A("s"); var r = A("r"); var t = A("t");
        return All("F", W(), All("s", Call("Set", R()), All("r", Call("Set", R()), All("t", R(),
            Imp(Ands(Call("ContinuousOn", Uncurry(f), Product(s, r)),
                new Formula.Relation(t, FormulaRelationOperator.MemberOf, s)),
                Call("ContinuousOn", Apply(f, t), r))))));
    }
    private static Formula ZeroFormula()
    {
        var y = A("Y"); var z = A("Z"); var t = A("t"); var cap = A("T"); var k = A("K");
        var closed = Call("Set.Icc", D(0), cap); var inside = Call("Set.Ioo", D(0), cap);
        return All("Y", Fns(), All("Z", Fns(), All("T", R(), All("K", R(),
            Imp(Ands(Call("ContinuousOn", y, closed),
                All("t", R(), Imp(new Formula.Relation(t, FormulaRelationOperator.MemberOf, inside),
                    Call("HasDerivAt", y, Apply(z, t), t))),
                All("t", R(), Imp(new Formula.Relation(t, FormulaRelationOperator.MemberOf, inside),
                    Leq(Apply(z, t), Mul(k, Apply(y, t))))), Eq(Apply(y, D(0)), D(0)),
                All("t", R(), Imp(new Formula.Relation(t, FormulaRelationOperator.MemberOf, closed), Leq(D(0), Apply(y, t))))),
                All("t", R(), Imp(new Formula.Relation(t, FormulaRelationOperator.MemberOf, closed), Eq(Apply(y, t), D(0)))))))));
    }
    private static Formula RegularSliceFormula() => All("w", W(), All("t", R(),
        Imp(Ands(Regular(A("w")), Leq(D(0), A("t"))), Call("Continuous", Apply(A("w"), A("t"))))));
    private static Formula EnergyContinuousFormula() => All("w", W(),
        Imp(Regular(A("w")), Call("ContinuousOn", E(A("w")), Call("Set.Ici", D(0)))));
    private static Formula NonnegativeFormula() => All("w", W(), All("t", R(), Leq(D(0), E(A("w"), A("t")))));
    private static Formula PdeEnergyFormula()
    {
        var w = A("w"); var t = A("t"); var d = A("D"); var q = A("Q"); var x = A("x");
        return All("w", W(), All("t", R(), All("D", R(), All("Q", Fns(),
            Imp(Ands(Regular(w), Lt(D(0), t), Call("Continuous", q),
                All("x", R(), Eq(Dt(w, t, x), Add(Mul(d, Dxx(w, t, x)), Apply(q, x))))),
                Call("HasDerivAt", E(w), Sub(Mul(D(2), Interval(Mul(Value(w, t, x), Apply(q, x)))),
                    Mul(Mul(D(2), d), Interval(Pow(Dx(w, t, x), 2)))), t))))));
    }
    private static Formula DecayFormula()
    {
        var w = A("w"); var d = A("D"); var m = A("mu");
        return All("w", W(), All("D", R(), All("mu", R(),
            Imp(Ands(Regular(w), Lt(D(0), d), Leq(D(0), m), Leq(m, d), SpatialPde(w, d, m), Odd(w)), LimitZero(E(w))))));
    }
    private static Formula SubFormula() => All("f", W(), All("g", W(),
        Imp(Ands(Regular(A("f")), Regular(A("g"))), Regular(Lam("t", R(), Lam("x", R(),
            Sub(Value(A("f"), A("t"), A("x")), Value(A("g"), A("t"), A("x")))))))));
    private static Formula ReflectFormula() => All("w", W(), Imp(Regular(A("w")),
        Regular(Lam("t", R(), Lam("x", R(), Value(A("w"), A("t"), Minus(A("x"))))))));
    private static Formula Combo() => Lam("t", R(), Lam("x", R(), Add(Add(
        Mul(A("a"), Value(A("f"), A("t"), A("x"))), Mul(A("b"), Value(A("g"), A("t"), A("x")))), A("c"))));
    private static Formula AffineFormula() => All("f", W(), All("g", W(), All("a", R(), All("b", R(), All("c", R(),
        Imp(Ands(Regular(A("f")), Regular(A("g"))), Regular(Combo())))))));
    private static Formula AffineDerivativeFormula()
    {
        var f = A("f"); var g = A("g"); var a = A("a"); var b = A("b"); var t = A("t"); var x = A("x");
        return All("f", W(), All("g", W(), All("a", R(), All("b", R(), All("c", R(), All("t", R(), All("x", R(),
            Imp(Ands(Regular(f), Regular(g), Lt(D(0), t)), Ands(
                Eq(Dt(Combo(), t, x), Add(Mul(a, Dt(f, t, x)), Mul(b, Dt(g, t, x)))),
                Eq(Dxx(Combo(), t, x), Add(Mul(a, Dxx(f, t, x)), Mul(b, Dxx(g, t, x)))))))))))));
    }

    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula A(string name) => F.Id(name);
    private static Formula Named(string name)
    {
        var items = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Eq(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Equal, r);
    private static Formula Leq(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, r);
    private static Formula Lt(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThan, r);
    private static Formula Add(Formula l, Formula r) => new Formula.Binary(l, FormulaBinaryOperator.Add, r);
    private static Formula Sub(Formula l, Formula r) => new Formula.Binary(l, FormulaBinaryOperator.Subtract, r);
    private static Formula Mul(Formula l, Formula r) => new Formula.Binary(l, FormulaBinaryOperator.Multiply, r);
    private static Formula Pow(Formula b, byte p) => new Formula.Power(b, D(p));
    private static Formula Minus(Formula f) => new Formula.Negate(f);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula p, Formula q) =>
        new Formula.Logic(Parenthesized(p), FormulaLogicOperator.Implies, Parenthesized(q));
    private static Formula Conj(Formula p, Formula q) =>
        new Formula.Logic(Parenthesized(p), FormulaLogicOperator.And, Parenthesized(q));
    private static Formula Iff(Formula p, Formula q) =>
        new Formula.Logic(Parenthesized(p), FormulaLogicOperator.Iff, Parenthesized(q));
    private static Formula Ands(params Formula[] ps) => ps.Aggregate(Conj);
    private static Formula Ty(params Formula[] types) => types.Length == 1 ? types[0] :
        new Formula.TypeArrow(types[0], Ty(types.Skip(1).ToArray()));
    private static Formula Lam(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Named("fun"), Sp, A(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula W() => Ty(R(), R(), R());
    private static Formula Fns() => Ty(R(), R());
    private static Formula PiR() => Named("Real.pi");
    private static Formula Period() => Mul(D(2), PiR());
    private static Formula Interval(Formula body) =>
        Seq(Int, Underscore, Grp(Minus(PiR())), Caret, Grp(PiR()), Sp, body, Sp, A("dx"));
    private static Formula Value(Formula w, Formula t, Formula x) => Apply(w, t, x);
    private static Formula Dt(Formula w, Formula t, Formula x) =>
        Call("deriv", Lam("r", R(), Value(w, A("r"), x)), t);
    private static Formula Dx(Formula w, Formula t, Formula x) => Call("deriv", Apply(w, t), x);
    private static Formula Dxx(Formula w, Formula t, Formula x) =>
        Call("deriv", Call("deriv", Apply(w, t)), x);
    private static Formula Uncurry(Formula w) => Call("Function.uncurry", w);
    private static Formula Product(Formula l, Formula r) => Seq(l, Sp, Times, Sp, r);
    private static Formula Strip(bool positive) => Product(Call(positive ? "Set.Ioi" : "Set.Ici", D(0)), Named("Set.univ"));
    private static Formula Cont(Formula w, bool positive) => Call("ContinuousOn", Uncurry(w), Strip(positive));
    private static Formula PosTime(Formula body) => All("t", R(), Imp(Lt(D(0), A("t")), body));
    private static Formula NonnegTime(Formula body) => All("t", R(), Imp(Leq(D(0), A("t")), body));
    private static Formula SpatialPde(Formula w, Formula d, Formula m) => PosTime(All("x", R(),
        Eq(Dt(w, A("t"), A("x")), Add(Mul(d, Dxx(w, A("t"), A("x"))),
            Mul(m, Sub(Value(w, A("t"), A("x")), Pow(Value(w, A("t"), A("x")), 3)))))));
    private static Formula Odd(Formula w) => PosTime(All("x", R(),
        Eq(Value(w, A("t"), Minus(A("x"))), Minus(Value(w, A("t"), A("x"))))));
    private static Formula LimitZero(Formula f) => Call("Tendsto", f, Named("Filter.atTop"), Call("nhds", D(0)));
}
