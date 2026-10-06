using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CosineCutoffKernelDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/Asymptotics/CosineCutoffKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual finite cosine cutoff is the ordinary inverse Fourier integral of its closed reciprocal-frequency symbol.",
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
                    + "The ordinary/L2 inverse identification, the all-L2 convolution operator, "
                    + "the positive-Ci cutoff limit, and the original weighted-operator and Gaussian path conclusions remain separate obligations."))),
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
}
