using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics.CosineCutoffKernel;

internal sealed class GaussianWeightDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/Asymptotics/CosineCutoffKernel/GaussianWeight.";
    private static Formula Id(string name) => F.Id(name);
    private static Formula Reals => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Arrow(Formula source, Formula target) => F.Grp(F.Seq(source, F.To, F.Sp, target));
    private static Formula Pair => Call("Product", Reals, Reals);
    private static Formula RealFunction => Arrow(Reals, Reals);
    private static Formula Volume => Id("volume");
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Neg(Formula a) => F.Seq(F.Minus, F.Grp(a));
    private static Formula Sq(Formula a) => Multiply(a, a);
    private static Formula Norm(Formula a) => Call("norm", a);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (int i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula.BoundVariable B(string name, Formula type) => new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [B(name, type)], body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        F.Seq(F.Open, F.Id(name), F.Colon, F.Sp, type, F.Sp, F.Mapsto, F.Sp, body, F.Close);
    private static Formula App(Formula function, Formula argument) => Call("apply", function, argument);
    private static Formula App2(Formula function, Formula first, Formula second) => App(App(function, first), second);
    private static Formula Coe(Formula value) => Call("coeFn", value);
    private static Formula AE(Formula a, Formula b, Formula measure) => Call("AEEq", a, b, measure);
    private static Formula AEAll(Formula measure, Formula predicate) => Call("AlmostEverywhere", measure, predicate);
    private static Formula Integral(Formula function, Formula measure) => Call("integral", function, measure);
    private static Formula Mem2(Formula function, Formula measure) => Call("MemLp", function, F.D(2), measure);
    private static Formula ToLp(Formula proof, Formula function) => Call("toLp", proof, function);
    private static Formula CLM(Formula source, Formula target) => Call("ContinuousLinearMap", Reals, source, target);
    private static Formula Compose(Formula a, Formula b) => Call("compose", a, b);
    private static Formula Tendsto(Formula function, Formula filter, Formula limit) =>
        Call("Tendsto", function, filter, Call("nhds", limit));
    private static Formula A => Div(Add(F.D(1), Id("r")), F.D(2));
    private static Formula Beta => Div(Subtract(F.D(1), Id("r")), F.D(2));
    private static Formula C0 => Div(F.D(1), Multiply(Multiply(F.D(4), F.Pi), Call("sqrt", Multiply(A, Beta))));
    private static Formula Kappa => Add(Div(F.D(1), A), Div(Sq(Id("alpha")), Beta));
    private static Formula Rho(Formula x) => Multiply(C0, Call("exp", Neg(Div(Multiply(Kappa, Sq(x)), F.D(2)))));
    private static Formula Mu => Call("withDensity", Volume, Lambda("x", Reals, Call("ennrealOfReal", Rho(Id("x")))));
    private static Formula MuProd => Call("productMeasure", Mu, Mu);
    private static Formula HR => Call("Lp", Reals, F.D(2), Volume);
    private static Formula HW => Call("Lp", Reals, F.D(2), Mu);
    private static Formula HK => Call("Lp", Reals, F.D(2), MuProd);
    private static Formula G0 => Multiply(Sq(C0), Call("sqrt", Div(F.Pi, Kappa)));
    private static Formula Gaussian(Formula z) => Multiply(G0, Call("exp", Neg(Div(Multiply(Kappa, Sq(z)), F.D(4)))));
    private static Formula DifferenceLift(Formula q) => Lambda("z", Pair,
        App(q, Subtract(Call("first", Id("z")), Call("second", Id("z")))));
    private static Formula DensityForward(Formula f) => Lambda("x", Reals,
        Multiply(Call("sqrt", Rho(Id("x"))), App(f, Id("x"))));
    private static Formula DensityBackward(Formula f) => Lambda("x", Reals,
        Div(App(f, Id("x")), Call("sqrt", Rho(Id("x")))));
    private static Formula Convolution(Formula q, Formula f, Formula measure) => Lambda("x", Reals,
        Integral(Lambda("y", Reals, Multiply(App(q, Subtract(Id("x"), Id("y"))), App(f, Id("y")))), measure));
    private static Formula Parameters(Formula body) => F.Disp(All(
        Implies(Lt(F.D(0), Id("r")), Implies(Lt(Id("r"), F.D(1)), body)), B("r", Reals), B("alpha", Reals)));

    private static Formula FactoryFormula()
    {
        Formula t = Id("T"), k = Id("K"), l = Id("L"), f = Id("f"), ks = Id("Ks"), i = Id("i");
        Formula row = Lambda("y", Reals,
            Multiply(App(Coe(k), Call("pair", Id("x"), Id("y"))), App(Coe(f), Id("y"))));
        Formula representation = All(AE(Coe(App2(t, k, f)), Lambda("x", Reals, Integral(row, Mu)), Mu),
            B("K", HK), B("f", HW));
        Formula lipschitz = All(Le(Norm(Subtract(App(t, k), App(t, l))), Norm(Subtract(k, l))), B("K", HK), B("L", HK));
        Formula continuous = All(Implies(Tendsto(ks, Id("filter"), k),
            Tendsto(Lambda("i", Id("iota"), App(t, App(ks, i))), Id("filter"), App(t, k))),
            B("iota", Id("Type")), B("filter", Call("Filter", Id("iota"))), B("Ks", Arrow(Id("iota"), HK)), B("K", HK));
        Formula rawRow = Lambda("y", Reals,
            Multiply(App(Id("k"), Call("pair", Id("x"), Id("y"))), App(Id("g"), Id("y"))));
        Formula representatives = All(And(
            AEAll(Mu, Lambda("x", Reals, Call("Integrable", rawRow, Mu))),
            AE(Lambda("x", Reals, Integral(rawRow, Mu)), Coe(App2(t, k, f)), Mu)),
            B("K", HK), B("f", HW), B("k", Arrow(Pair, Reals)), B("g", RealFunction),
            B("hk", AE(Id("k"), Coe(k), MuProd)), B("hg", AE(Id("g"), Coe(f), Mu)));
        Formula closedBound = All(Implies(Tendsto(ks, Id("filter"), k),
            Implies(Call("Eventually", Id("filter"), Lambda("i", Id("iota"), Le(Norm(App(t, App(ks, i))), Id("bound")))),
                Le(Norm(App(t, k)), Id("bound")))),
            B("iota", Id("Type")), B("filter", Call("Filter", Id("iota"))),
            B("nonemptyFilter", Call("NeBot", Id("filter"))),
            B("Ks", Arrow(Id("iota"), HK)), B("K", HK), B("bound", Reals));
        return Parameters(Exists("T", CLM(HK, CLM(HW, HW)),
            And(representation, lipschitz, continuous, representatives, closedBound)));
    }

    private static Formula DensityFormula()
    {
        Formula u = Id("U"), inverse = Call("symm", u);
        return Parameters(Exists("U", Call("LinearIsometryEquiv", Reals, HW, HR), And(
            All(AE(Coe(App(u, Id("f"))), DensityForward(Coe(Id("f"))), Volume), B("f", HW)),
            All(AE(Coe(App(inverse, Id("h"))), DensityBackward(Coe(Id("h"))), Mu), B("h", HR)))));
    }

    private static Formula KernelFormula()
    {
        Formula q = Id("q"), p = Id("p"), k = Id("K"), l = Id("L"), ks = Id("Ks"), i = Id("i");
        Formula correlation = All(Equal(Integral(Lambda("x", Reals,
            Multiply(Rho(Id("x")), Rho(Subtract(Id("x"), Id("z"))))), Volume), Gaussian(Id("z"))), B("z", Reals));
        Formula self = Equal(G0, Integral(Lambda("x", Reals, Sq(Rho(Id("x")))), Volume));
        Formula build = All(Exists("K", HK, And(
            AE(Coe(k), DifferenceLift(q), MuProd),
            Equal(Sq(Norm(k)), Integral(Lambda("z", Reals, Multiply(Sq(App(q, Id("z"))), Gaussian(Id("z")))), Volume)),
            Le(Sq(Norm(k)), Multiply(G0, Sq(Norm(ToLp(Id("hq"), q))))))),
            B("q", RealFunction), B("measurableQ", Call("Measurable", q)), B("hq", Mem2(q, Volume)));
        Formula pair = All(Le(Sq(Norm(Subtract(k, l))),
            Multiply(G0, Sq(Norm(Subtract(ToLp(Id("hq"), q), ToLp(Id("hp"), p)))))),
            B("q", RealFunction), B("p", RealFunction),
            B("measurableQ", Call("Measurable", q)), B("measurableP", Call("Measurable", p)),
            B("hq", Mem2(q, Volume)), B("hp", Mem2(p, Volume)), B("K", HK), B("L", HK),
            B("hK", AE(Coe(k), DifferenceLift(q), MuProd)), B("hL", AE(Coe(l), DifferenceLift(p), MuProd)));
        Formula familyQ = App(q, i), familyHQ = App(Id("hq"), i);
        Formula convergence = All(Implies(
            Tendsto(Lambda("i", Id("iota"), ToLp(familyHQ, familyQ)), Id("filter"), ToLp(Id("hp"), p)),
            Tendsto(ks, Id("filter"), k)),
            B("iota", Id("Type")), B("filter", Call("Filter", Id("iota"))),
            B("q", Arrow(Id("iota"), RealFunction)), B("p", RealFunction),
            B("measurableQ", All(Call("Measurable", familyQ), B("i", Id("iota")))),
            B("measurableP", Call("Measurable", p)),
            B("hq", All(Mem2(familyQ, Volume), B("i", Id("iota")))), B("hp", Mem2(p, Volume)),
            B("Ks", Arrow(Id("iota"), HK)), B("K", HK),
            B("hKs", All(AE(Coe(App(ks, i)), DifferenceLift(familyQ), MuProd), B("i", Id("iota")))),
            B("hK", AE(Coe(k), DifferenceLift(p), MuProd)));
        return Parameters(And(correlation, self, build, pair, convergence));
    }

    private static Formula ConjugacyFormula()
    {
        Formula q = Id("q"), c = Id("C"), t = Id("T"), u = Id("U"), m = Id("M"), inverse = Call("symm", u);
        Formula conclusion = Exists("M", CLM(HR, HR), And(
            All(AE(Coe(App(m, Id("h"))), DensityForward(Coe(Id("h"))), Volume), B("h", HR)),
            Le(Norm(m), Call("sqrt", C0)),
            Equal(Compose(Call("asCLM", u), Compose(t, Call("asCLM", inverse))), Compose(m, Compose(c, m))),
            Le(Norm(t), Multiply(C0, Norm(c)))));
        return Parameters(All(conclusion,
            B("q", RealFunction), B("hq", Mem2(q, Volume)), B("C", CLM(HR, HR)),
            B("hC", All(AE(Coe(App(c, Id("h"))), Convolution(q, Coe(Id("h")), Volume), Volume), B("h", HR))),
            B("T", CLM(HW, HW)),
            B("hT", All(AE(Coe(App(t, Id("f"))), Convolution(q, Coe(Id("f")), Mu), Mu), B("f", HW))),
            B("U", Call("LinearIsometryEquiv", Reals, HW, HR)),
            B("hU", All(AE(Coe(App(u, Id("f"))), DensityForward(Coe(Id("f"))), Volume), B("f", HW))),
            B("hUinv", All(AE(Coe(App(inverse, Id("h"))), DensityBackward(Coe(Id("h"))), Mu), B("h", HR)))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian density gives the actual integral-kernel factory, density isometry, difference-kernel estimates, and convolution conjugacy.",
        H("Gaussian-weighted integral operators"), Blocks(
            Describe.Lean(DescribeId.Create("gaussian-weighted-integral-factory"),
                DeclarationHandle.Create(Module + "weighted_integral_operator"), H("The actual L2 kernel factory"),
                StatementSource.FromAuthor(FactoryFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the original parameters 0<r<1 and arbitrary real alpha, set a=(1+r)/2, b=(1-r)/2, c0=1/(4*pi*sqrt(a*b)), kappa=1/a+alpha^2/b, rho(x)=c0*exp(-kappa*x^2/2), and mu=volume.withDensity(ofReal(rho)). The displayed T is a continuous linear map from real L2(mu times mu) to continuous operators on real L2(mu). Its representatives are the actual kernel integrals, it is 1-Lipschitz in the kernel, it preserves arbitrary filter limits, and its raw-representative clause proves row integrability and equality for any almost-everywhere-equal representatives. An eventual uniform bound passes to the limit only under the displayed nonempty-filter hypothesis."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gaussian-density-unitary"),
                DeclarationHandle.Create(Module + "density_unitary"), H("An onto density isometry"),
                StatementSource.FromAuthor(DensityFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With exactly the same density and measure, the real linear isometry equivalence U multiplies a weighted-L2 representative by sqrt(rho) almost everywhere for Lebesgue measure. Its inverse divides a Lebesgue-L2 representative by sqrt(rho) almost everywhere for mu. The strictly positive Gaussian density makes both directions lawful; surjectivity and the inverse formula are included in the equivalence, not assumed separately."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gaussian-weighted-difference-kernel"),
                DeclarationHandle.Create(Module + "gaussian_weighted_kernel"), H("Gaussian difference kernels and their limits"),
                StatementSource.FromAuthor(KernelFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Put g0=c0^2*sqrt(pi/kappa). The Gaussian overlap integral is g0*exp(-kappa*z^2/4), including its exact z=0 square-density identity. Every measurable real L2 function q supplies an actual weighted product-L2 kernel represented by q(x-y), with the displayed exact norm-square integral and norm bound. Every pair of such actual kernels obeys the difference estimate. For any index type and filter, convergence of the actual unweighted L2 classes implies convergence of every represented weighted kernel family. All representative equalities, measurability assumptions and MemLp witnesses are quantified explicitly; the family limit does not require a nonempty filter."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gaussian-density-convolution-conjugacy"),
                DeclarationHandle.Create(Module + "cutoff_conjugacy"), H("Conjugacy of the same integral operators"),
                StatementSource.FromAuthor(ConjugacyFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same real function q supplies both the unweighted operator C and weighted operator T through their actual ordinary integral representative equations. The equivalence U has the displayed density and inverse-density formulas. Multiplication by sqrt(rho) defines M with norm at most sqrt(c0); the exact equation U*T*U-inverse=M*C*M yields norm(T) at most c0*norm(C). This supplier assumes the two displayed integral representations for its arbitrary input operators. The original finite-cutoff client separately constructs those actual operators before applying it; no assumed representation replaces that client construction."))), DescribeRole.Theorem))));
}
