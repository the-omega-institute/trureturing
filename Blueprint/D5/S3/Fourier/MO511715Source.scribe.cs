using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class MO511715SourceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/MO511715Source.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact Euclidean five-dimensional cutoff series and a lower bound for its nested time integral.",
        H("The five-dimensional cutoff series in MathOverflow 511715"),
        Blocks(
            Paragraph(Text(
                "The source is mathex, Bound of series, MathOverflow question 511715, revision 2, "
                + "https://mathoverflow.net/questions/511715/bound-of-series, licensed CC BY-SA 4.0. "
                + "Its scalar field and vector norm are not specified. Here the vector norm is Euclidean, "
                + "and both real and complex cutoffs are included. Constants may depend on the individually "
                + "fixed cutoff. These conventions do not assert the author's unspecified intent.")),
            Paragraph(Text(
                "Write Z for the lattice of five integer coordinates and E for Euclidean five-space. "
                + "The map embed casts coordinates from Z into E. Set frequency(k)=norm(2*pi*embed(k)). "
                + "The legal masks take values in [0,1], and a nonzero value at (k,l) implies "
                + "(9/64)*norm(k)<=norm(l)<=(64/9)*norm(k). Both support boundaries are inclusive.")),
            Item("time-integral", "timeIntegral", "The original time integral", TimeFormula(),
                "The two inner intervals are independent, so their Cartesian product is the full square. "
                + "For nonnegative time, the interval integrals agree with Lebesgue integration on the "
                + "displayed closed intervals; changing endpoints has measure zero. No ordering between "
                + "the inner variables is imposed.", DescribeRole.Definition),
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
    private static Formula Pow(Formula a, int n) => new Formula.Power(a, F.D(n));
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
            Eq(Call("timeIntegral", q, l, a, b), body)))));
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
}
