using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class MO511715SourceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/MO511715Source.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact Euclidean five-dimensional cutoff series and the failure of its uniform cutoff estimate.",
        H("The five-dimensional cutoff series in MathOverflow 511715"),
        Blocks(
            Paragraph(Text(
                "The source is mathex, Bound of series, MathOverflow question 511715, revision 2, "
                + "https://mathoverflow.net/questions/511715/bound-of-series, licensed CC BY-SA 4.0. "
                + "Its scalar field and vector norm are not specified. Here the vector norm is Euclidean, "
                + "and both real and complex cutoffs are included. Constants may depend on the individually "
                + "fixed cutoff. The question does not give a full cutoff quantifier prefix, scalar types "
                + "or signs for C and delta, or a definition of R_+. The claim below uses finite C>=0, "
                + "delta>0, and nonnegative time, including the explicitly requested zero endpoint. "
                + "These disclosed conventions do not resolve the author's unspecified intent.")),
            Paragraph(Text(
                "Write Z for the lattice of five integer coordinates and E for Euclidean five-space. "
                + "The map embed casts coordinates from Z into E. Set frequency(k)=norm(2*pi*embed(k)). "
                + "The legal masks take values in [0,1], and a nonzero value at (k,l) implies "
                + "(9/64)*norm(k)<=norm(l)<=(64/9)*norm(k). Both support boundaries are inclusive.")),
            Item("time-integral", "timeIntegral", "The original time integral", TimeFormula(),
                "The source definition integrates directly over the complete closed square with product "
                + "Lebesgue measure. Its exponential is continuous and integrable on that compact set. "
                + "Fubini's theorem and the zero measure of interval endpoints give the displayed iterated "
                + "form for nonnegative time. No ordering between the inner variables is imposed.",
                DescribeRole.Definition),
            Item("kernel", "kernel", "The source kernel", KernelFormula(),
                "All Fourier factors are retained: the prefactor is the squared frequency and each "
                + "decay rate is the fourth power of its own frequency. The definition divides by no mode.",
                DescribeRole.Definition),
            Item("cutoff-weight", "cutoffWeight", "The two absolute-square cutoff factors", WeightFormula(),
                "Scalar norms mean real absolute value or complex modulus. The same cutoff and scale "
                + "are used in both factors.", DescribeRole.Definition),
            Item("phi", "phi", "The complete ordered-pair lattice sum", PhiFormula(),
                "The sum ranges over all ordered pairs in Z times Z, including all zero modes. "
                + "At a positive scale, compact support restricts both difference coordinates to bounded "
                + "sets. The integer-to-Euclidean embedding is part of each cutoff argument.", DescribeRole.Definition),
            Item("delta", "delta", "The zero-output subtraction", DeltaFormula(),
                "The same mask and cutoff occur in the value at u and the value at zero.", DescribeRole.Definition),
            Item("claim", "claim", "The complete uniform estimate in both scalar readings", ClaimFormula(),
                "A smooth cutoff is compactly supported, infinitely differentiable over the reals, and "
                + "equals one at zero. For each fixed cutoff, C is finite and nonnegative and the real "
                + "exponent is positive. The estimate quantifies every legal mask, every nonnegative time, "
                + "every lattice output, and both positive scales. Coincident scales, time zero and all "
                + "positive scales remain included. No symmetry, regularity or partition identity is "
                + "imposed on the mask, and no radiality, monotonicity or common support radius is imposed "
                + "on the cutoff.", DescribeRole.Definition),
            Item("time-integral-lower", "time_integral_ge", "A lower bound from a genuine time subregion",
                LowerFormula(),
                "Restrict the outer variable to [1-h,1] and each inner variable to [alpha-h,alpha]. "
                + "The assumption h<=1/2 puts this subregion inside the original square. Its iterated "
                + "volume is h cubed. On this same subregion, 1-alpha<=h and "
                + "1+alpha-2*v<=3*h. Thus the total decay exponent is at most one. Continuity supplies "
                + "integrability on every interval, and nonnegativity permits restriction of each integral.",
                DescribeRole.Theorem),
            Item("finite-cutoff-support", "cutoff_finite_support", "Finite support at every positive scale",
                FiniteSupportFormula(),
                "Compact support gives a radius R outside which the cutoff vanishes. A nonzero weight "
                + "forces both Euclidean difference vectors to have norm less than R/e. Each integer "
                + "coordinate is bounded by that norm, so the two vectors belong to finite coordinate "
                + "boxes. The inverse map (a,b) to (a+b,b) gives a finite set of original ordered indices. "
                + "Every source sum is therefore summable at positive scale, without a convergence assumption.",
                DescribeRole.Theorem),
            Paragraph(Text(
                "Let e be the first coordinate unit. The selected mask is one precisely when k+l=e "
                + "and the two inclusive source support inequalities hold; it is zero otherwise. "
                + "At the actual source arguments, k+l=n. Thus every output except e vanishes, "
                + "and delta at e is exactly phi at e. This is one fixed mask for every scale and cutoff.")),
            Paragraph(Text(
                "The box B(N) consists of all integer vectors with N<=a(i)<2*N in each of the five "
                + "coordinates. It has exactly N to the fifth power elements. Its ordered pair block "
                + "has N to the tenth power elements. Write D=2*pi, eta=1/(20000*D^4), "
                + "kappa=D^2*exp(-1)*eta^3 and c=kappa/16. Both constants are strictly positive.")),
            Item("kernel-block-lower", "kernel_block_lower", "The actual kernel on a lattice block",
                KernelLowerFormula(),
                "For a,b in B(N), their norms are at most 5*N. The norm of a+b is between 4*N and "
                + "9*N, while the norm of e-a-b is between N and 10*N. The triangle inequalities "
                + "also give both original support comparisons, so the selected mask equals one. "
                + "Take h=eta/N^4 in the time-integral bound. The decay budget is at most "
                + "(10^4+6*5^4)/20000=11/16. Multiplying by the actual frequency-squared prefactor "
                + "gives kappa/N^10. No hypothesized kernel estimate is used.", DescribeRole.Theorem),
            Item("dyadic-growth", "phi_dyadic_growth", "Simultaneous cutoff control across disjoint blocks",
                GrowthFormula(),
                "Continuity and normalization give a radius 0<rho<=1 on whose closed ball the cutoff "
                + "modulus is at least one half, for either scalar field. At scale rho/(5*2^J), "
                + "both cutoff factors obey this bound simultaneously on every B(2^j) with j<=J. "
                + "Their squared product is at least 1/16. The half-open dyadic boxes are pairwise "
                + "disjoint, and the exact ordered-index bijection preserves their disjointness. "
                + "Each block contributes at least c; nonnegative omitted terms give c*(J+1).",
                DescribeRole.Theorem),
            Item("result", "result", "Negation of the complete conventional source claim",
                F.Seq(F.Neg, F.Sp, Id("claim")),
                "The stronger obstruction holds for every individually fixed continuous-at-zero "
                + "normalized compact cutoff over "
                + "either the real or complex scalars, and every pair of finite real numbers C and delta, "
                + "without sign restrictions. Keep that same cutoff and the same legal selected mask "
                + "on both sides, with time one and output e. The reference scale is two; the comparison "
                + "scale epsilon=rho/(5*2^J) satisfies 0<epsilon<=rho/5<=1/5. Thus both scales are "
                + "strictly positive and distinct, and 1<=abs(2-epsilon)<=2. For every real delta, "
                + "abs(2-epsilon)^delta<=H=max(1,2^delta): monotonicity in the base gives the bound "
                + "when delta>=0, and a base at least one gives a bound of one when delta<=0. "
                + "Consequently C*abs(2-epsilon)^delta<=max(C,0)*H. The fixed reference value "
                + "M=phi(2,1,e) is finite. Choose J so that c*(J+1)>M+max(C,0)*H. The growth bound "
                + "then makes the actual absolute delta difference strictly larger than the proposed "
                + "right side. This includes zero and negative exponents and constants. "
                + "Taking nonnegative C and a positive exponent refutes the conventional estimate "
                + "for every such cutoff. A standard smooth real bump then negates the conjunction "
                + "claim. Every smooth "
                + "normalized compact cutoff in either scalar reading satisfies the stronger lemma's "
                + "hypotheses. The source's unspecified norm, typing and authorial intent remain "
                + "unresolved conventions; the conclusion does not assume additional mask structure.",
                DescribeRole.Theorem))));

    private static DocumentBlock Item(string id, string declaration, string title, Formula formula,
        string commentary, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(F.Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(commentary))), role);

    private static Formula R => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Z => new Formula.Power(F.Seq(F.Mathbb, F.Grp(F.Id("Z"))), F.D(5));
    private static Formula E => new Formula.Power(R, F.D(5));
    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, byte n) => new Formula.Power(a, F.D(n));
    private static Formula Fn(Formula a, Formula b) => F.Seq(a, F.Sp, F.To, F.Sp, b);
    private static Formula Integral(string variable, Formula a, Formula b, Formula body) =>
        F.Seq(F.Int, F.Underscore, F.Grp(a), F.Caret, F.Grp(b), F.Sp, body,
            F.Sp, Id("d"), Id(variable));
    private static Formula Freq(Formula k) => Call("frequency", k);

    private static Formula TimeFormula()
    {
        Formula q = Id("q"), l = Id("L"), a = Id("A"), b = Id("B");
        Formula t = Id("t"), v = Id("v"), w = Id("w");
        Formula exponent = Sub(Sub(F.D(0), Mul(a, Sub(Add(q, t), Mul(F.D(2), v)))),
            Mul(b, Sub(Add(q, t), Mul(F.D(2), w))));
        Formula body = Integral("t", F.D(0), q,
            Mul(Call("exp", Sub(F.D(0), Mul(l, Sub(q, t)))),
                Integral("v", F.D(0), t, Integral("w", F.D(0), t, Call("exp", exponent)))));
        return All("q", R, All("L", R, All("A", R, All("B", R,
            Imp(Le(F.D(0), q), Eq(Call("timeIntegral", q, l, a, b), body))))));
    }

    private static Formula KernelFormula()
    {
        Formula p = Id("p"), q = Id("q"), n = Id("n"), a = Id("a"), b = Id("b");
        Formula k = Sub(n, a);
        return All("p", Fn(Z, Fn(Z, R)), All("q", R, All("n", Z, All("a", Z, All("b", Z,
            Eq(Call("kernel", p, q, n, a, b),
                Mul(Mul(Pow(Freq(k), 2), Call("p", k, a)),
                    Call("timeIntegral", q, Pow(Freq(k), 4), Pow(Freq(Sub(a, b)), 4), Pow(Freq(b), 4)))))))));
    }

    private static Formula WeightFormula()
    {
        Formula f = Id("F"), z = Id("z"), e = Id("e"), a = Id("a"), b = Id("b");
        return All("F", Call("NormedAddCommGroup"), All("z", Fn(E, f), All("e", R,
            All("a", Z, All("b", Z, Eq(Call("cutoffWeight", z, e, a, b),
                Mul(Pow(Call("norm", Call("z", Mul(e, Call("embed", Sub(a, b))))), 2),
                    Pow(Call("norm", Call("z", Mul(e, Call("embed", b)))), 2))))))));
    }

    private static Formula PhiFormula()
    {
        Formula f = Id("F"), z = Id("z"), p = Id("p"), e = Id("e"), q = Id("q"), n = Id("n");
        Formula a = Id("a"), b = Id("b");
        Formula sum = F.Seq(F.Sum, F.Underscore,
            F.Grp(F.Seq(F.Open, a, F.Comma, b, F.Close, F.Sp, F.InMacro, F.Sp, Call("Product", Z, Z))),
            F.Sp, Mul(Call("kernel", p, q, n, a, b), Call("cutoffWeight", z, e, a, b)));
        return All("F", Call("NormedAddCommGroup"), All("z", Fn(E, f), All("p", Fn(Z, Fn(Z, R)),
            All("e", R, All("q", R, All("n", Z, Eq(Call("phi", z, p, e, q, n), sum)))))));
    }

    private static Formula DeltaFormula()
    {
        Formula f = Id("F"), z = Id("z"), p = Id("p"), e = Id("e"), r = Id("r"), u = Id("u");
        return All("F", Call("NormedAddCommGroup"), All("z", Fn(E, f), All("p", Fn(Z, Fn(Z, R)),
            All("e", R, All("r", R, All("u", Z, Eq(Call("delta", z, p, e, r, u),
                Sub(Call("phi", z, p, e, r, u), Call("phi", z, p, e, r, F.D(0))))))))));
    }

    private static Formula Estimate(Formula z)
    {
        Formula c = Id("C"), d = Id("d"), p = Id("p"), r = Id("r"), u = Id("u"), a = Id("a"), b = Id("b");
        Formula bound = Le(new Formula.Absolute(Sub(Call("delta", z, p, b, r, u),
            Call("delta", z, p, a, r, u))),
            Mul(c, new Formula.Power(new Formula.Absolute(Sub(b, a)), d)));
        return Exists("C", R, And(Le(F.D(0), c), Exists("d", R, And(Lt(F.D(0), d),
            All("p", Fn(Z, Fn(Z, R)), Imp(Call("LegalMask", p), All("r", R,
                Imp(Le(F.D(0), r), All("u", Z, All("a", R, All("b", R,
                    Imp(Lt(F.D(0), a), Imp(Lt(F.D(0), b), bound)))))))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula z = Id("z");
        Formula real = All("z", Fn(E, R), Imp(Call("SmoothCutoff", z), Estimate(z)));
        Formula complex = All("z", Fn(E, F.Seq(F.Mathbb, F.Grp(Id("C")))),
            Imp(Call("SmoothCutoff", z), Estimate(z)));
        return Iff(Id("claim"), And(real, complex));
    }

    private static Formula LowerFormula()
    {
        Formula l = Id("L"), a = Id("A"), b = Id("B"), h = Id("h");
        Formula budget = Le(Mul(Add(Add(l, Mul(F.D(3), a)), Mul(F.D(3), b)), h), F.D(1));
        Formula conditions = And(Le(F.D(0), l), And(Le(F.D(0), a), And(Le(F.D(0), b),
            And(Lt(F.D(0), h), And(Le(h, new Formula.Fraction(F.D(1), F.D(2))), budget)))));
        return All("L", R, All("A", R, All("B", R, All("h", R,
            Imp(conditions, Le(Mul(Call("exp", Sub(F.D(0), F.D(1))), Pow(h, 3)),
                Call("timeIntegral", F.D(1), l, a, b)))))));
    }

    private static Formula FiniteSupportFormula()
    {
        Formula f = Id("F"), z = Id("z"), e = Id("e");
        Formula weight = F.Seq(F.Open, Id("a"), F.Comma, Id("b"), F.Close,
            F.Sp, F.Mapsto, F.Sp, Call("cutoffWeight", z, e, Id("a"), Id("b")));
        return All("F", Call("NormedAddCommGroup"), All("z", Fn(E, f), All("e", R,
            Imp(And(Call("HasCompactSupport", z), Lt(F.D(0), e)),
                Call("Finite", Call("support", weight))))));
    }

    private static Formula KernelLowerFormula()
    {
        Formula n = Id("N"), a = Id("a"), b = Id("b");
        Formula hypotheses = And(Le(F.D(1), n), And(
            new Formula.Relation(a, FormulaRelationOperator.MemberOf, Call("blockBox", n)),
            new Formula.Relation(b, FormulaRelationOperator.MemberOf, Call("blockBox", n))));
        return All("N", F.Seq(F.Mathbb, F.Grp(Id("N"))), All("a", Z, All("b", Z,
            Imp(hypotheses, Le(new Formula.Fraction(Call("kernelConstant"), new Formula.Power(n, F.D(1, 0))),
                Call("kernel", Call("selectedMask"), F.D(1), Call("firstUnit"), Add(a, b), b))))));
    }

    private static Formula GrowthFormula()
    {
        Formula f = Id("F"), z = Id("z"), r = Id("r"), j = Id("J");
        Formula hypotheses = And(Call("ContinuousAt", z, F.D(0)),
            And(Eq(Call("z", F.D(0)), F.D(1)), Call("HasCompactSupport", z)));
        Formula scale = new Formula.Fraction(r, Mul(F.D(5), new Formula.Power(F.D(2), j)));
        Formula conclusion = Exists("r", R, And(Lt(F.D(0), r), And(Le(r, F.D(1)),
            All("J", F.Seq(F.Mathbb, F.Grp(Id("N"))),
                Le(Mul(Call("blockConstant"), Add(j, F.D(1))),
                    Call("phi", z, Call("selectedMask"), scale, F.D(1), Call("firstUnit")))))));
        return All("F", Call("RCLike"), All("z", Fn(E, f), Imp(hypotheses, conclusion)));
    }
}
