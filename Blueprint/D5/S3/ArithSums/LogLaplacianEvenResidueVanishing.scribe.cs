using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class LogLaplacianEvenResidueVanishingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/rosenzweigstanfill2026loglaplacians");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Rosenzweig-Stanfill residue bracket vanishes for every even index.",
        H("Even residues of the logarithmic Laplacian"),
        Blocks(
            Definition("bellProfiles", "Bounded Bell profiles", ProfilesFormula(),
                "Equation (1.21), page 6, requires the sum of the profile entries to be k and their weighted sum to be n. Fin(L) means the integers 0 through L-1; val is the natural value of a finite index. natSub denotes truncated natural subtraction. Each entry is at most k because the entries sum to k."),
            Definition("bell", "Partial ordinary Bell polynomials", BellFormula(),
                "Equation (1.20), page 6, is the multinomial profile sum for the partial ordinary Bell polynomial. The sequence s has complex values. Every natural coefficient and factorial in complex arithmetic is cast to C."),
            Definition("negativePolylog", "Negative integral polylogarithms", PolylogFormula(),
                "Equation (2.49), page 13, recursively applies the Euler derivative z times deriv(f,z), starting with z/(1-z). iterate applies the displayed operator j times. deriv is the complex derivative, including its totalized value outside differentiability."),
            Definition("s2", "The Bernoulli sequence", SequenceFormula(),
                "Theorem 1.5, page 4: \"where the sequence S₂ satisfies sₖ⁽²⁾ = −Bₖ/k, k ∈ N.\" Here B denotes the pinned Bernoulli number with B₁ = −1/2. Only positive entries occur in the Bell sum; the unused zero entry is set to zero. The separately occurring Euler constant s₀⁽²⁾ is not an argument of that sum."),
            Definition("p", "The residue polynomials", PolynomialFormula(),
                "Definition 1.1, page 2: \"Given a sequence of numbers, S, indexed over a set J ⊇ N, we define\" the finite sum (1.5). This definition specializes that sum to S₂. The carrier for t and the polynomial value is C; j and k are natural numbers."),
            Definition("c", "The primary recursive coefficients", CoefficientsFormula(),
                "Equation (1.14), page 4, defines the primary array, including its separate Bernoulli value at a = pi/2. Here a encodes alpha. ite selects its second argument when its first argument holds and its third otherwise. The exponent ite(Even(j+1),1,0) is exactly (1+(-1)^(j+1))/2. The finite index q in Fin(j) replaces the paper's index from 1 through j by val(q)+1. The real sine and the real ratio cos(2a)/sin(2a) are embedded into C; exp is the complex exponential after a is embedded into C."),
            Definition("d", "The finite difference array", DifferenceFormula(),
                "Equation (1.14), page 4, defines d(j,0) as the Kronecker delta and gives the displayed finite sum when j >= k >= 1. The extension for k > j is zero and is never used by the residue sums. All quotients here are complex division; powers retain natural exponents. In the innermost factor ell-v is complex subtraction after both natural indices are cast, so it can be negative; natSub is used only for the natural binomial and exponent indices."),
            Definition("b", "The coefficient convolution", ConvolutionFormula(),
                "Equation (1.14), page 4, convolves d(k+j,k) with c(i-2j). natDiv(i,2) means floor(i/2), using natural integer division."),
            Definition("w", "Squared Pochhammer weights", WeightFormula(),
                "The weight in (1.13), page 4, is ((1/2)_k)^2/(k!)^2. The Pochhammer factor is the product over q from 0 through k-1; the empty product is one."),
            Definition("A", "The inner residue sum", InnerFormula(),
                "This notation abbreviates exactly the inner finite sum of (1.13), page 4. The upper bound natDiv(ell,2) is floor(ell/2)."),
            Definition("paperBracket", "The bracket in (1.13)", BracketFormula(),
                "The two finite sums are the bracket in (1.13), page 4. The first interval includes 1 and m+1, and range(m+1) includes 0 through m. The external factor 2 exp(gamma_E m)/pi is nonzero and therefore has no effect on vanishing."),
            Definition("claim", "Open Problem 1.6(iv)", ClaimDefinitionFormula(),
                "Open Problem 1.6, page 4: \"Consider the notation of Theorem 1.5. Then the following are conjectured to be true:\" Clause (iv): \"For every α ∈ (0, π), (1.13) is equal to zero whenever m ≥ 0 is even.\" The encoding uses m : N, so m >= 0 includes zero, and a : R for α. paperBracket is the bracket of (1.13), with its literal recursive c-array and partial ordinary Bell polynomial definitions."),
            Describe.Lean(
                DescribeId.Create("rs16-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Vanishing for every even index"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Centering the primary coefficient series by exp(-s/2) makes it even: its square is the inverse of 2 cosh(s)-2 cos(2a). The b-array convolution multiplies that series by an even series. Bernoulli translation to 1/2 then makes the residue functional annihilate the odd derivative for every even m. These are identities of formal power-series coefficients; no analytic convergence hypothesis is needed."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string heading, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("rs16-" + (name == "s2" ? "sequence" : name.ToLowerInvariant())),
            DeclarationHandle.Create(Prefix + name), H(heading), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula ProfilesFormula()
    {
        var n = F.Id("n"); var k = F.Id("k"); var j = F.Id("j"); var i = F.Id("i");
        var size = Add(Call("natSub", n, k), D(1));
        var index = Call("Fin", size);
        var profiles = new Formula.TypeArrow(index, Call("Fin", Add(k, D(1))));
        var entry = Call("val", new Formula.Apply(j, [i]));
        var predicate = And(Equal(SumOver("i", index, entry), k),
            Equal(SumOver("i", index, Mul(Add(Call("val", i), D(1)), entry)), n));
        var conditionSet = Call("filter", Call("univ", profiles),
            Seq(Parenthesized(Seq(j, Colon, Parenthesized(profiles))), Sp, Mapsto, Sp, Parenthesized(predicate)));
        return Disp(All("n", N(), All("k", N(), Equal(Call("bellProfiles", n, k), conditionSet))));
    }
    private static Formula BellFormula()
    {
        var n = F.Id("n"); var k = F.Id("k"); var s = F.Id("s"); var j = F.Id("j"); var i = F.Id("i");
        var index = Call("Fin", Add(Call("natSub", n, k), D(1)));
        var entry = Call("val", new Formula.Apply(j, [i]));
        var body = Mul(Div(Cast(Factorial(k), C()), ProductOver("i", index, Cast(Factorial(entry), C()))),
            ProductOver("i", index, Pow(new Formula.Apply(s, [Add(Call("val", i), D(1))]), entry)));
        return Disp(All("n", N(), All("k", N(), All("s", new Formula.TypeArrow(N(), C()),
            Equal(Call("bell", n, k, s), SumOver("j", Call("bellProfiles", n, k), body))))));
    }
    private static Formula PolylogFormula()
    {
        var j = F.Id("j"); var z = F.Id("z"); var f = F.Id("f"); var x = F.Id("x");
        var step = Seq(Parenthesized(Seq(f, Colon, new Formula.TypeArrow(C(), C()))), Sp, Mapsto, Sp,
            Parenthesized(Seq(Parenthesized(Seq(x, Colon, C())), Sp, Mapsto, Sp, Mul(x, Call("deriv", f, x)))));
        var start = Seq(Parenthesized(Seq(x, Colon, C())), Sp, Mapsto, Sp, Div(x, Sub(D(1), x)));
        return Disp(All("j", N(), All("z", C(), Equal(Call("negativePolylog", j, z),
            Call("iterate", Parenthesized(step), j, Parenthesized(start), z)))));
    }
    private static Formula SequenceFormula()
    {
        var n = F.Id("n");
        return Disp(All("n", N(), Equal(Call("s2", n),
            Call("ite", Equal(n, D(0)), D(0), Div(Negative(Cast(Call("B", n), C())), Cast(n, C()))))));
    }
    private static Formula PolynomialFormula()
    {
        var j = F.Id("j"); var t = F.Id("t"); var k = F.Id("k");
        return Disp(All("j", N(), All("t", C(), Equal(Call("p", j, t),
            SumOver("k", Call("range", Add(j, D(1))),
                Mul(Mul(Div(Pow(Negative(D(1)), k), Cast(Factorial(k), C())), Call("bell", j, k, F.Id("s2"))), Pow(t, k)))))));
    }
    private static Formula CoefficientsFormula()
    {
        var a = F.Id("a"); var j = F.Id("j"); var q = F.Id("q");
        var succ = Add(j, D(1)); var twoA = Mul(D(2), a);
        var first = All("a", R(), Equal(Call("c", a, D(0)), Div(D(1), Mul(D(2), Cast(Call("sin", a), C())))));
        var center = Div(Mul(Sub(Pow(D(2), Add(j, D(2))), D(1)), Cast(Call("B", Add(j, D(2))), C())), Cast(Factorial(Add(j, D(2))), C()));
        var cot = Div(Call("cos", twoA), Call("sin", twoA));
        var coeff = Div(Negative(Pow(Mul(F.Id("I"), Cast(cot, C())), Call("ite", Call("Even", succ), D(1), D(0)))), Cast(Factorial(succ), C()));
        var term = Mul(coeff, Call("negativePolylog", succ, Call("exp", Mul(Mul(D(2), Cast(a, C())), F.Id("I")))));
        var convolution = SumOver("q", Call("Fin", j),
            Mul(Call("c", a, Add(Call("val", q), D(1))), Call("c", a, Call("natSub", j, Call("val", q)))));
        var recursive = Mul(Cast(Call("sin", a), C()), Sub(term, convolution));
        var second = All("a", R(), All("j", N(), Equal(Call("c", a, succ),
            Call("ite", Equal(a, Div(Pi, D(2))), center, recursive))));
        return Disp(new Formula.Aligned([first, second]));
    }
    private static Formula DifferenceFormula()
    {
        var a = F.Id("a"); var j = F.Id("j"); var k = F.Id("k"); var ell = F.Id("ell"); var v = F.Id("v");
        var inner = SumOver("v", Call("range", Add(Mul(D(2), ell), D(1))),
            Mul(Mul(Pow(Negative(D(1)), v), Cast(Call("binomial", Mul(D(2), ell), v), C())),
                Pow(Sub(Cast(ell, C()), Cast(v, C())), Mul(D(2), j))));
        var summand = Mul(Div(Div(Mul(Cast(Call("binomial", Call("natSub", ell, D(1)), Call("natSub", k, D(1))), C()),
            Pow(Negative(D(1)), Call("natSub", ell, k))), Pow(D(4), ell)),
            Pow(Cast(Call("sin", a), C()), Mul(D(2), ell))), inner);
        var finite = Mul(Div(D(1), Cast(Factorial(Mul(D(2), j)), C())), SumOver("ell", Call("Icc", k, j), summand));
        var body = Call("ite", Equal(k, D(0)), Call("ite", Equal(j, D(0)), D(1), D(0)),
            Call("ite", LeqFormula(k, j), finite, D(0)));
        return Disp(All("a", R(), All("j", N(), All("k", N(), Equal(Call("d", a, j, k), body)))));
    }
    private static Formula ConvolutionFormula()
    {
        var a = F.Id("a"); var i = F.Id("i"); var k = F.Id("k"); var j = F.Id("j");
        return Disp(All("a", R(), All("i", N(), All("k", N(), Equal(Call("b", a, i, k),
            SumOver("j", Call("range", Add(Call("natDiv", i, D(2)), D(1))),
                Mul(Call("d", a, Add(k, j), k), Call("c", a, Call("natSub", i, Mul(D(2), j))))))))));
    }
    private static Formula WeightFormula()
    {
        var k = F.Id("k"); var q = F.Id("q");
        return Disp(All("k", N(), Equal(Call("w", k),
            Div(Pow(ProductOver("q", Call("range", k), Add(Div(D(1), D(2)), Cast(q, C()))), D(2)), Pow(Cast(Factorial(k), C()), D(2))))));
    }
    private static Formula InnerFormula()
    {
        var a = F.Id("a"); var ell = F.Id("ell"); var k = F.Id("k");
        return Disp(All("a", R(), All("ell", N(), Equal(Call("A", a, ell),
            SumOver("k", Call("range", Add(Call("natDiv", ell, D(2)), D(1))),
                Mul(Call("w", k), Call("b", a, Call("natSub", ell, Mul(D(2), k)), k)))))));
    }
    private static Formula BracketFormula()
    {
        var m = F.Id("m"); var a = F.Id("a"); var ell = F.Id("ell");
        Formula Term(Formula degree) => Mul(Mul(Mul(Pow(Negative(D(1)), ell), Cast(Factorial(ell), C())),
            Call("p", Call("natSub", degree, ell), Negative(Cast(m, C())))), Call("A", a, ell));
        var first = SumOver("ell", Call("Icc", D(1), Add(m, D(1))), Term(Add(m, D(1))));
        var second = SumOver("ell", Call("range", Add(m, D(1))), Term(m));
        return Disp(All("m", N(), All("a", R(), Equal(Call("paperBracket", m, a), Add(first, Mul(Div(D(1), D(2)), second))))));
    }
    private static Formula ClaimDefinitionFormula() => Disp(Equal(F.Id("claim"), Parenthesized(ClaimBody())));
    private static Formula ClaimBody()
    {
        var m = F.Id("m"); var a = F.Id("a");
        return All("m", N(), ImpliesFormula(Call("Even", m), All("a", R(),
            ImpliesFormula(Less(D(0), a), ImpliesFormula(Less(a, Pi), Equal(Call("paperBracket", m, a), D(0)))))));
    }

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula C() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LeqFormula(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula ImpliesFormula(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Div(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Slash, Sp, Parenthesized(right));
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Negative(Formula value) => Seq(Minus, Parenthesized(value));
    private static Formula Factorial(Formula value) => Seq(Parenthesized(value), Bang);
    private static Formula SumOver(string name, Formula range, Formula body) => Seq(Sum, Underscore, Grp(F.Id(name), Sp, InMacro, Sp, range), Sp, Parenthesized(body));
    private static Formula ProductOver(string name, Formula range, Formula body) => Seq(Prod, Underscore, Grp(F.Id(name), Sp, InMacro, Sp, range), Sp, Parenthesized(body));
}
