using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class IterateProductTwentyFiveModFiveDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2026a396795");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every coefficient above degree one in OEIS A396795 is divisible by five.",
        H("Hanna's Iterate-Product Congruence Modulo Five"),
        Blocks(
            Paragraph(Text("Paul D. Hanna's OEIS A396795 entry states the generating "
                + "equation and conjecture recorded in hanna2026a396795. All series below "
                + "have integer coefficients except in the two lemmas over an arbitrary "
                + "commutative ring R. All coefficient and iterate indices are natural numbers. "
                + "The generating series is normalized by zero constant coefficient and "
                + "coefficient one at degree one.")),
            Paragraph(Text("PowerSeries(Z) denotes the formal power-series ring with "
                + "indeterminate X. The iterate operation is defined in "
                + "D5/S1/Recurrence/Invariants/CompositionalIterateCongruence: "
                + "iterate(Z,f,0)=X and iterate(Z,f,j+1)=iterate(Z,f,j).subst(f). "
                + "Thus iterate(Z,f,2)=f(f(X)) when the constant coefficient is zero. "
                + "Powers and products are ordinary power-series operations. The operator "
                + "choose selects a witness of the displayed proved existential proposition. "
                + "C embeds a scalar as a constant series, subst is formal substitution, "
                + "and natCast(R,k) is the natural-number cast into R. Type ranges over "
                + "types in any universe; CommRing(R) supplies the commutative ring structure.")),
            Node("subst_annihilate", "Scalar annihilation survives substitution", AnnihilateFormula(),
                "Factor u to the power k minus v to the power k by u-v. The scalar r "
                + "annihilates each such difference, hence every coefficient in the "
                + "difference of substitutions. The zero constant coefficients justify "
                + "computing substitution coefficients by finite sums."),
            Node("nilpotent_iterate", "Iteration with a square-zero scalar", NilpotentFormula(),
                "For any commutative ring and any scalar r with r*r=0, scalar "
                + "annihilation makes each substitution add the same term C(r)*b. "
                + "Induction gives the formula for every natural iterate index."),
            Node("iterate_product_lift", "Square-zero lifting for two iterate indices", GeneralLiftFormula(),
                "Write f=X+C(m)*b by exact coefficientwise division and map to ZMod(m^2). "
                + "There m*m=0, so the two iterates are X+C(i*m)*b and X+C(j*m)*b. "
                + "Their quadratic correction vanishes because it carries m*m. Their "
                + "linear correction vanishes because m divides i+j. Mapping back proves "
                + "integer coefficient divisibility, including modulus zero."),
            Node("generatingSeries", "The normalized generating series", GeneratingFormula(),
                "Existence follows from successive coefficient corrections starting at X. "
                + "At degree n greater than one, the error at degree n+1 is divided by "
                + "five using integer division. The lifting lemma makes this exact and "
                + "makes the correction divisible by five. The stabilized coefficients "
                + "give an integer series satisfying all three existential clauses.",
                DescribeRole.Definition),
            Node("a", "The coefficient sequence", CoefficientFormula(),
                "The integer a(n) is the degree-n coefficient of generatingSeries. "
                + "Its constant coefficient is zero and its degree-one coefficient is one.",
                DescribeRole.Definition),
            Node("generating_equation", "The OEIS equation and normalization", EquationFormula(),
                "The constructed series satisfies the product equation as a formal "
                + "power-series identity, together with both normalization conditions. "
                + "Witness selection preserves these three proved properties."),
            Node("generating_unique", "Uniqueness of the normalized integer solution", UniqueFormula(),
                "If two normalized series agree below degree n greater than one, their "
                + "second and third iterates differ at degree n by twice and three times "
                + "their coefficient difference. Their products differ at degree n+1 "
                + "by five times that difference. "
                + "Equal products force equal coefficients over the integers, and strong "
                + "induction proves equality of the series."),
            Node("hanna_conjecture", "The A396795 divisibility conjecture", ConjectureFormula(),
                "Induct on n and truncate the solution below degree n. The earlier "
                + "coefficients make this prefix congruent to X modulo five. The lifting "
                + "lemma makes its product error divisible by twenty-five. Comparing the prefix "
                + "with the solution using the coefficient perturbation gives twenty-five "
                + "dividing 5a(n), hence five dividing a(n), for every n greater than one.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a396795-iterate-product-twenty-five-mod-five"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a396795-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula X() => F.Id("X");
    private static Formula Generating() => Named("generatingSeries");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Divides(Formula left, Formula right) => Seq(left, Sp, Mid, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Product(Formula f) => Mul(
        Call("iterate", Integers(), f, D(2)), Call("iterate", Integers(), f, D(3)));
    private static Formula RightSide() => Add(Power(X(), D(2)), Mul(Call("C", D(2, 5)), Power(X(), D(3))));
    private static Formula NormalizedEquation(Formula f) => Seq(
        Parenthesized(Equal(Product(f), RightSide())), Sp, Land, Sp,
        Parenthesized(Seq(Parenthesized(Equal(Call("constantCoeff", f), D(0))), Sp, Land, Sp,
            Parenthesized(Equal(Call("coeff", D(1), f), D(1))))));

    private static Formula AnnihilateFormula()
    {
        var r = F.Id("r");
        var ring = F.Id("R");
        var f = F.Id("f");
        var u = F.Id("u");
        var v = F.Id("v");
        var scalar = Call("C", r);
        return Disp(Seq(Bound("R", Named("Type")),
            Implication(Call("CommRing", ring), Seq(Bound("r", ring),
                Bound("f", Call("PowerSeries", ring)), Bound("u", Call("PowerSeries", ring)),
                Bound("v", Call("PowerSeries", ring)),
                Implication(Equal(Call("constantCoeff", u), D(0)),
                    Implication(Equal(Call("constantCoeff", v), D(0)),
                        Implication(Equal(Mul(scalar, Parenthesized(Subtract(u, v))), D(0)),
                            Equal(Mul(scalar, Parenthesized(Subtract(
                                Call("subst", f, u), Call("subst", f, v)))), D(0)))))))));
    }

    private static Formula NilpotentFormula()
    {
        var r = F.Id("r");
        var ring = F.Id("R");
        var b = F.Id("b");
        var j = F.Id("j");
        var series = Add(X(), Mul(Call("C", r), b));
        return Disp(Seq(Bound("R", Named("Type")),
            Implication(Call("CommRing", ring), Seq(Bound("r", ring),
                Implication(Equal(Mul(r, r), D(0)), Seq(Bound("b", Call("PowerSeries", ring)),
                    Implication(Equal(Call("constantCoeff", series), D(0)),
                        Seq(Bound("j", Naturals()), Equal(Call("iterate", ring, series, j),
                            Add(X(), Mul(Call("C", Mul(Call("natCast", ring, j), r)), b)))))))))));
    }

    private static Formula GeneralLiftFormula()
    {
        var m = F.Id("m");
        var f = F.Id("f");
        var i = F.Id("i");
        var j = F.Id("j");
        var n = F.Id("n");
        var integerM = Call("natCast", Integers(), m);
        var congruence = Seq(Bound("n", Naturals()),
            Divides(integerM, Call("coeff", n, Subtract(f, X()))));
        var product = Mul(Call("iterate", Integers(), f, i), Call("iterate", Integers(), f, j));
        return Disp(Seq(Bound("m", Naturals()), Bound("f", Series()),
            Implication(Equal(Call("constantCoeff", f), D(0)),
                Implication(congruence, Seq(Bound("i", Naturals()), Bound("j", Naturals()),
                    Implication(Divides(m, Parenthesized(Add(i, j))), Seq(Bound("n", Naturals()),
                        Divides(Power(integerM, D(2)),
                            Call("coeff", n, Subtract(product, Power(X(), D(2))))))))))));
    }

    private static Formula GeneratingFormula() => Disp(Equal(Generating(),
        Call("choose", Seq(Exists, Sp, F.Id("f"), Colon, Sp, Series(), Comma, Sp,
            Parenthesized(NormalizedEquation(F.Id("f")))))));

    private static Formula CoefficientFormula() => Disp(Seq(Bound("n", Naturals()),
        Equal(Call("a", F.Id("n")), Call("coeff", F.Id("n"), Generating()))));

    private static Formula EquationFormula() => Disp(Seq(
        Parenthesized(Equal(Call("constantCoeff", Generating()), D(0))), Sp, Land, Sp,
        Parenthesized(Seq(
            Parenthesized(Equal(Call("coeff", D(1), Generating()), D(1))), Sp, Land, Sp,
            Parenthesized(Equal(Product(Generating()), RightSide()))))));

    private static Formula UniqueFormula() => Disp(Seq(Bound("f", Series()),
        Implication(Equal(Product(F.Id("f")), RightSide()),
            Implication(Equal(Call("constantCoeff", F.Id("f")), D(0)),
                Implication(Equal(Call("coeff", D(1), F.Id("f")), D(1)),
                    Equal(F.Id("f"), Generating()))))));

    private static Formula ConjectureFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(1), Sp, Lt, Sp, F.Id("n")),
            Divides(D(5), Call("a", F.Id("n"))))));
}
