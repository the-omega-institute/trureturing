using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CosineCutoffKernelDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/Asymptotics/CosineCutoffKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual finite cosine cutoff has ordinary and L2 inverse identities, an all-L2 convolution operator, and an actual weighted integral client.",
        H("The Finite Cosine Cutoff Kernel"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-cosine-cutoff-kernel"),
            DeclarationHandle.Create(Module + "result"),
            H("Every positive lower cutoff and every larger finite upper cutoff"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The real physical kernel is the actual oriented interval integral below. "
                    + "The symbol is complex valued and has closed frequency endpoints. All integrals use Lebesgue measure."),
                    Math(KernelDefinition()), Ref(Module + "kernel")),
                Paragraph(Math(SymbolDefinition()), Ref(Module + "symbol")),
                Paragraph(Text("FourierInv denotes the ordinary inverse integral with the positive phase, "
                    + "dual to the forward exp(-2*pi*i*x*xi) convention. Its exact integral is displayed here."),
                    Math(InverseDefinition())),
                Paragraph(Text("The positive and reflected negative bands are disjoint because c is positive. "
                    + "Pairing their exponential phases gives twice the real cosine. "
                    + "The substitution t=2*pi*xi gives the physical interval integral with its minus-two coefficient.")),
                Paragraph(Text("The symbol is measurable, Lebesgue integrable, and in complex L2. "
                    + "Its pointwise norm is at most 2*pi/c. For every real M at least N, "
                    + "the pointwise difference of the symbols with upper cutoffs M and N is at most 2*pi/N.")),
                Paragraph(Text("At x=0 the physical kernel is -2*log(N/c). At N=c the physical kernel "
                    + "and every ordinary real weighted integral action are zero. The closed symbol is zero "
                    + "almost everywhere, and is nonzero at both frequencies c/(2*pi) and -c/(2*pi). "
                    + "The weighted zero action quantifies over every pair of real functions rho and f.")),
                Paragraph(Text("This statement establishes ordinary finite inverse integration and finite symbol estimates. "
                    + "The public finite-window theorem also identifies the actual L2 inverse representative "
                    + "of this same symbol with the complex-valued kernel in L2, "
                    + "including its almost-everywhere representative equality."),
                    Ref(Module + "actual_cutoff_inverse")),
                Paragraph(Text("The positive-Ci cutoff limit and the original Gaussian series and path conclusions remain separate obligations."))),
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-finite-cutoff-l2-inverse"),
                DeclarationHandle.Create(Module + "actual_cutoff_inverse"),
                H("The actual L2 inverse and its kernel representative"),
                StatementSource.FromAuthor(ActualInverseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For c>0 and c<=N, let m be the existing closed-band symbol "
                        + "and q(x)=ofReal(kernel(c,N,x)). The statement supplies proofs hm and hq "
                        + "that these two specific functions belong to complex L2(volume).")),
                    Paragraph(Text("L2FourierInverse denotes the inverse of Lp.fourierTransformₗᵢ ℝ ℂ. "
                        + "toLp(h,f) is the L2 class constructed from the displayed MemLp witness; "
                        + "coeFn is its measurable representative. The first equality is almost everywhere "
                        + "for volume. The second is equality of L2 elements.")),
                    Paragraph(Text("This theorem identifies the inverse transform of m itself. "
                        + "It makes no assertion about the convolution of q with arbitrary L2 inputs, "
                        + "weighted operators, or the positive-Ci limit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-finite-cutoff-all-l2-convolution"),
                DeclarationHandle.Create(Module + "actual_cutoff_convolution"),
                H("The ordinary convolution on every complex L2 input"),
                StatementSource.FromAuthor(ActualConvolutionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("HC is Lp(C,2,volume), and CLMC(HC,HC) is its space of complex "
                        + "continuous linear maps. L2Fourier and L2FourierInverse are the mutually inverse "
                        + "Lp Fourier isometries with the exp(-2*pi*i*x*xi) forward convention.")),
                    Paragraph(Text("Every input f belongs to the full complex L2 space. For every real x, "
                        + "the actual integral row q(x-y)f(y) is integrable. The displayed MemLp witnesses "
                        + "supply the spatial integral and the frequency product as L2 elements. "
                        + "Both are identified with the same operator output, with the inverse transform "
                        + "applied to the frequency product.")),
                    Paragraph(Text("The nested estimate quantifies over every real M>=N. Its operator D "
                        + "is identified almost everywhere with the ordinary convolution using kernel(c,M). "
                        + "Only the frequency functions m, phase*m and m*L2Fourier(f) use bounded support."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-weighted-finite-cutoff"),
                DeclarationHandle.Create(Module + "actual_weighted_cutoff"),
                H("The actual weighted integral operator and its density conjugacy"),
                StatementSource.FromAuthor(ActualWeightedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The parameters are r and alpha with 0<r<1. Define a=(1+r)/2, "
                        + "b=(1-r)/2, c0=1/(4*pi*sqrt(a*b)), kappa=1/a+alpha^2/b, "
                        + "rho(x)=c0*exp(-kappa*x^2/2), and mu=volume.withDensity(ofReal(rho)). "
                        + "The formula expands these definitions, with ennrealOfReal denoting ENNReal.ofReal. HR=Lp(R,2,volume), Hmu=Lp(R,2,mu).")),
                    Paragraph(Text("T is obtained from the actual L2 integral-kernel factory applied to "
                        + "K(x,y)=kernel(c,N,x-y). Its ordinary weighted integral representative and "
                        + "almost-everywhere row integrability are established before the conjugacy is used. "
                        + "No identity for T or C is required as a caller hypothesis.")),
                    Paragraph(Text("U is an onto real linear isometry between the two displayed measures; "
                        + "its inverse is also specified almost everywhere. M is multiplication by sqrt(rho). "
                        + "compose(A,B) means A after B, and asCLM denotes the continuous linear map "
                        + "underlying a linear isometry equivalence.")),
                    Paragraph(Text("This finite-cutoff statement does not pass to the positive-Ci limit "
                        + "or assert any Gaussian quadratic-series or path-limit conclusion."))),
                DescribeRole.Theorem))));

    private static Formula Reals => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Arrow(Formula a, Formula b) => F.Grp(F.Seq(a, F.To, F.Sp, b));
    private static Formula Negative(Formula a) => F.Seq(F.Minus, F.Grp(a));
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Positive(Formula a) =>
        new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, a);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (int i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
    private static Formula Lambda(string name, Formula domain, Formula body) =>
        F.Seq(F.Open, F.Id(name), F.Colon, F.Sp, domain, F.Sp, F.Mapsto, F.Sp, body, F.Close);
    private static Formula Integral(Formula variable, Formula body) =>
        F.Seq(F.Int, F.Underscore, F.Grp(Reals), F.Sp, body, F.Sp, F.Id("d"), variable);
    private static Formula IntervalIntegral(Formula lower, Formula upper, Formula variable, Formula body) =>
        F.Seq(F.Int, F.Underscore, F.Grp(lower), F.Caret, F.Grp(upper),
            F.Sp, body, F.Sp, F.Id("d"), variable);
    private static Formula TwoPi => Multiply(F.D(2), F.Pi);
    private static Formula Kernel(Formula c, Formula n, Formula x) => Call("kernel", c, n, x);
    private static Formula Symbol(Formula c, Formula n) => Call("symbol", c, n);
    private static Formula SymbolAt(Formula c, Formula n, Formula xi) => Call("symbol", c, n, xi);
    private static Formula Norm(Formula value) => Call("norm", value);

    private static Formula KernelDefinition()
    {
        Formula c = F.Id("c"), n = F.Id("N"), x = F.Id("x"), t = F.Id("t");
        return Equal(Kernel(c, n, x), Multiply(Negative(F.D(2)),
            IntervalIntegral(c, n, t, new Formula.Fraction(Call("cos", Multiply(t, x)), t))));
    }
    private static Formula SymbolDefinition()
    {
        Formula c = F.Id("c"), n = F.Id("N"), xi = F.Id("xi");
        Formula absolute = new Formula.Absolute(xi);
        Formula condition = And(Le(new Formula.Fraction(c, TwoPi), absolute),
            Le(absolute, new Formula.Fraction(n, TwoPi)));
        return Equal(SymbolAt(c, n, xi), Call("ite", condition,
            Call("ofReal", Negative(new Formula.Fraction(F.D(1), absolute))), F.D(0)));
    }
    private static Formula InverseDefinition()
    {
        Formula c = F.Id("c"), n = F.Id("N"), x = F.Id("x"), xi = F.Id("xi");
        Formula phase = Multiply(Call("ofReal", Multiply(TwoPi, Multiply(xi, x))), F.Id("i"));
        return Equal(Call("FourierInv", Symbol(c, n), x),
            Integral(xi, Multiply(Call("exp", phase), SymbolAt(c, n, xi))));
    }
    private static Formula TheoremFormula()
    {
        Formula c = F.Id("c"), n = F.Id("N"), m = F.Id("M"),
            x = F.Id("x"), y = F.Id("y"), xi = F.Id("xi");
        Formula h = Symbol(c, n), a = new Formula.Fraction(c, TwoPi);
        Formula weightedZero = All("rho", Arrow(Reals, Reals),
            All("f", Arrow(Reals, Reals), All("x", Reals,
                Equal(Integral(y, Multiply(Multiply(Kernel(c, n, Subtract(x, y)),
                    Call("f", y)), Call("rho", y))), F.D(0)))));
        Formula degenerate = Implies(Equal(c, n), And(
            All("x", Reals, Equal(Kernel(c, n, x), F.D(0))), weightedZero,
            Call("AEEq", h, Lambda("xi", Reals, F.D(0)), F.Id("volume")),
            NotEqual(SymbolAt(c, n, a), F.D(0)),
            NotEqual(SymbolAt(c, n, Negative(a)), F.D(0))));
        Formula statement = And(Call("Measurable", h), Call("Integrable", h, F.Id("volume")),
            Call("MemLp", h, F.D(2), F.Id("volume")),
            All("xi", Reals, Le(Norm(SymbolAt(c, n, xi)), new Formula.Fraction(TwoPi, c))),
            All("M", Reals, Implies(Le(n, m), All("xi", Reals,
                Le(Norm(Subtract(SymbolAt(c, m, xi), SymbolAt(c, n, xi))),
                    new Formula.Fraction(TwoPi, n))))),
            All("x", Reals, Equal(Call("FourierInv", h, x), Call("ofReal", Kernel(c, n, x)))),
            Equal(Kernel(c, n, F.D(0)), Multiply(Negative(F.D(2)), Call("log", new Formula.Fraction(n, c)))),
            degenerate);
        return F.Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("c"), Reals),
             new Formula.BoundVariable(FormulaIdentifier.Create("N"), Reals)],
            Implies(Positive(c), Implies(Le(c, n), statement))));
    }

    private static Formula ActualInverseFormula()
    {
        Formula c = F.Id("c"), n = F.Id("N"), x = F.Id("x"),
            hm = F.Id("hm"), hq = F.Id("hq"), volume = F.Id("volume");
        Formula m = Symbol(c, n);
        Formula q = Lambda("x", Reals, Call("ofReal", Kernel(c, n, x)));
        Formula inverse = Call("L2FourierInverse", Call("toLp", hm, m));
        Formula conclusion = new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create("hm"), Call("MemLp", m, F.D(2), volume)),
             new Formula.BoundVariable(FormulaIdentifier.Create("hq"), Call("MemLp", q, F.D(2), volume))],
            And(Call("AEEq", Call("coeFn", inverse), q, volume),
                Equal(inverse, Call("toLp", hq, q))));
        return F.Disp(All("c", Reals, All("N", Reals,
            Implies(Positive(c), Implies(Le(c, n), conclusion)))));
    }

    private static Formula Complexes => F.Seq(F.Mathbb, F.Grp(F.Id("C")));
    private static Formula HC => Call("Lp", Complexes, F.D(2), F.Id("volume"));
    private static Formula HR => Call("Lp", Reals, F.D(2), F.Id("volume"));
    private static Formula CLM(Formula field, Formula source, Formula target) =>
        Call("ContinuousLinearMap", field, source, target);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
    private static Formula IntegralWith(Formula function, Formula measure) =>
        Call("integral", function, measure);
    private static Formula Compose(Formula a, Formula b) => Call("compose", a, b);
    private static Formula AE(Formula a, Formula b, Formula measure) => Call("AEEq", a, b, measure);

    private static Formula ActualConvolutionFormula()
    {
        Formula c = F.Id("c"), n = F.Id("N"), upper = F.Id("M"),
            x = F.Id("x"), y = F.Id("y"), xi = F.Id("xi"), f = F.Id("f"),
            op = F.Id("C"), d = F.Id("D"), hg = F.Id("hg"), hconv = F.Id("hconv"),
            volume = F.Id("volume");
        Formula q = Lambda("x", Reals, Call("ofReal", Kernel(c, n, x)));
        Formula row = Lambda("y", Reals,
            Multiply(Call("ofReal", Kernel(c, n, Subtract(x, y))), Call("f", y)));
        Formula conv = Lambda("x", Reals, IntegralWith(row, volume));
        Formula spectral = Lambda("xi", Reals,
            Multiply(SymbolAt(c, n, xi), Call("eval", Call("L2Fourier", f), xi)));
        Formula exact = Exists("hg", Call("MemLp", spectral, F.D(2), volume),
            Exists("hconv", Call("MemLp", conv, F.D(2), volume),
                And(AE(Call("coeFn", Call("C", f)), conv, volume),
                    Equal(Call("C", f), Call("toLp", hconv, conv)),
                    Equal(Call("C", f), Call("L2FourierInverse", Call("toLp", hg, spectral))))));
        Formula upperConv = Lambda("x", Reals, IntegralWith(Lambda("y", Reals,
            Multiply(Call("ofReal", Kernel(c, upper, Subtract(x, y))), Call("f", y))), volume));
        Formula nested = All("M", Reals, Implies(Le(n, upper),
            Exists("D", CLM(Complexes, HC, HC), And(
                All("f", HC, AE(Call("coeFn", Call("D", f)), upperConv, volume)),
                Le(Norm(Subtract(d, op)), new Formula.Fraction(TwoPi, n))))));
        Formula conclusion = And(Call("MemLp", q, F.D(2), volume),
            Exists("C", CLM(Complexes, HC, HC), And(
                All("f", HC, All("x", Reals, Call("Integrable", row, volume))),
                All("f", HC, exact), Le(Norm(op), new Formula.Fraction(TwoPi, c)), nested)));
        return F.Disp(All("c", Reals, All("N", Reals,
            Implies(Positive(c), Implies(Le(c, n), conclusion)))));
    }

    private static Formula ActualWeightedFormula()
    {
        Formula r = F.Id("r"), alpha = F.Id("alpha"), c = F.Id("c"), n = F.Id("N"),
            x = F.Id("x"), y = F.Id("y"), f = F.Id("f"), h = F.Id("h"),
            op = F.Id("C"), t = F.Id("T"), u = F.Id("U"), m = F.Id("M"),
            volume = F.Id("volume");
        Formula a = new Formula.Fraction(Add(F.D(1), r), F.D(2));
        Formula b = new Formula.Fraction(Subtract(F.D(1), r), F.D(2));
        Formula c0 = new Formula.Fraction(F.D(1),
            Multiply(Multiply(F.D(4), F.Pi), Call("sqrt", Multiply(a, b))));
        Formula kappa = Add(new Formula.Fraction(F.D(1), a),
            new Formula.Fraction(Multiply(alpha, alpha), b));
        Formula Rho(Formula z) => Multiply(c0, Call("exp",
            Negative(new Formula.Fraction(Multiply(kappa, Multiply(z, z)), F.D(2)))));
        Formula mu = Call("withDensity", volume,
            Lambda("x", Reals, Call("ennrealOfReal", Rho(x))));
        Formula hmu = Call("Lp", Reals, F.D(2), mu);
        Formula row = Lambda("y", Reals,
            Multiply(Kernel(c, n, Subtract(x, y)), Call("f", y)));
        Formula conv = Lambda("x", Reals, IntegralWith(row, volume));
        Formula weighted = Lambda("x", Reals, IntegralWith(row, mu));
        Formula uinv = Call("symm", u);
        Formula conclusion = Exists("C", CLM(Reals, HR, HR),
            Exists("T", CLM(Reals, hmu, hmu),
            Exists("U", Call("LinearIsometryEquiv", Reals, hmu, HR),
            Exists("M", CLM(Reals, HR, HR), And(
                All("f", HR, AE(Call("coeFn", Call("C", f)), conv, volume)),
                All("f", hmu, AE(Call("coeFn", Call("T", f)), weighted, mu)),
                All("f", hmu, Call("AlmostEverywhere", mu,
                    Lambda("x", Reals, Call("Integrable", row, mu)))),
                All("f", hmu, AE(Call("coeFn", Call("U", f)),
                    Lambda("x", Reals, Multiply(Call("sqrt", Rho(x)), Call("f", x))), volume)),
                All("h", HR, AE(Call("coeFn", Call("apply", uinv, h)),
                    Lambda("x", Reals, new Formula.Fraction(Call("h", x), Call("sqrt", Rho(x)))), mu)),
                All("h", HR, AE(Call("coeFn", Call("M", h)),
                    Lambda("x", Reals, Multiply(Call("sqrt", Rho(x)), Call("h", x))), volume)),
                Equal(Compose(Call("asCLM", u), Compose(t, Call("asCLM", uinv))),
                    Compose(m, Compose(op, m))),
                Le(Norm(op), new Formula.Fraction(TwoPi, c)),
                Le(Norm(m), Call("sqrt", c0)),
                Le(Norm(t), Multiply(c0, new Formula.Fraction(TwoPi, c))))))));
        return F.Disp(All("r", Reals, All("alpha", Reals,
            Implies(Positive(r), Implies(new Formula.Relation(r, FormulaRelationOperator.LessThan, F.D(1)),
            All("c", Reals, All("N", Reals,
                Implies(Positive(c), Implies(Le(c, n), conclusion)))))))));
    }
}
