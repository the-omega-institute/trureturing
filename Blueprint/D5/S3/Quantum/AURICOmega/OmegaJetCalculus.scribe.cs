using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class OmegaJetCalculusDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/AURICOmega/OmegaJetCalculus";

    public DocumentDefinition Create()
    {
        Formula a = F.Id("a"), b = F.Id("b"), f = F.Id("f"), g = F.Id("g");
        Formula x = F.Id("x"), h = F.Id("h"), n = F.Id("N"), k = F.Id("k");
        Formula zero = D(0), one = D(1), two = D(2), minusTwo = Negative(two);
        Formula jet = F.Id("Jet2"), coefficients = F.Id("JetSeq"), scalar = F.Id("IntRatio");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula eta = F.Id("eta"), cos = F.Id("Cos"), sin = F.Id("Sin"), atan = F.Id("Atan");
        Formula cayleyCos = F.Id("CayleyCos"), cayleySin = F.Id("CayleySin");
        Formula denominator = Add(one, Square(eta));
        Formula composed = Call("compose", g, f);
        Formula fidelityDen = Add(one, Square(x));
        Formula shifted = Add(x, h);
        Formula shiftedDen = Add(one, Square(shifted));
        Formula kappaJet = Call("kappaJetAt", x);
        Formula firstCayleyEq = Below(naturals, k, n,
            Equiv(Coeff(Mul(Deriv(f), denominator), k), Coeff(Mul(minusTwo, g), k)));
        Formula secondCayleyEq = Below(naturals, k, n,
            Equiv(Coeff(Mul(Deriv(g), denominator), k), Coeff(Mul(two, f), k)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Second-order jets in Chapter 32, section 32.7.3.1, the secant identity in section 32.7.5.3, and formal rational series in section 32.8.4.4.",
            H("Rational jet calculus and formal differential equations"),
            Blocks(
                Law("jet-increment-cube", "var_cube", "The jet increment cubes to zero",
                    Equiv(Cube(eta), zero),
                    "The variable is the second-order jet with coefficients (0, 1, 0). Multiplication retains degrees zero, one and two."),
                Law("jet-inversion", "mul_inv", "Inversion of a second-order jet",
                    All(["a"], jet, If(And(Call("Unit", Coeff(a, zero)),
                        And(Finite(Coeff(a, one)), Finite(Coeff(a, two)))),
                        Equiv(Mul(a, Call("inv", a)), one))),
                    "An invertible constant coefficient is a finite nonzero fraction. The inverse of a normalized jet 1 + u has coefficients obtained from 1 - u + u squared because u cubed vanishes."),
                Law("jet-chain-rule", "chain_rule", "First and second chain rules at zero shift",
                    All(["g", "f"], jet, If(And(Finite(Coeff(g, one)), And(Finite(Coeff(g, two)),
                        And(Finite(f), Equiv(Coeff(f, zero), zero)))),
                        And(Equiv(Call("first", composed), Mul(Call("first", g), Call("first", f))),
                            Equiv(Call("second", composed),
                                Add(Mul(Call("second", g), Square(Call("first", f))),
                                    Mul(Call("first", g), Call("second", f))))))),
                    "The outer jet is evaluated in the inner jet, whose constant coefficient is zero. The second derivative is twice the quadratic coefficient."),
                Law("fidelity-jet-coefficients", "kappa_jet", "The exact fidelity jet",
                    All(["x"], scalar, Equiv(kappaJet, Tuple(Call("kappa", x),
                        Div(Negative(Mul(two, x)), Square(fidelityDen)),
                        Div(Sub(Mul(D(3), Square(x)), one), Cube(fidelityDen))))),
                    "Inverting the jet of 1 + (x + eta) squared gives the three coefficients for kappa, where kappa(x) is the reciprocal of 1 + x squared."),
                Law("fidelity-jet-at-one", "kappa_jet_one", "The fidelity jet at one",
                    Equiv(Call("kappaJetAt", one), Tuple(Div(one, two), Negative(Div(one, two)), Div(one, D(4)))),
                    "The coefficient triple at one gives the value, the linear coefficient and the quadratic coefficient in that order."),
                Law("fidelity-secant-discrepancy", "kappa_secant_discrepancy", "The exact secant discrepancy",
                    All(["x", "h"], scalar, If(And(Finite(x), Call("Unit", h)),
                        Equiv(Sub(Div(Sub(Call("kappa", shifted), Call("kappa", x)), h), Call("first", kappaJet)),
                            Div(Mul(h, Sub(Add(Mul(D(3), Square(x)), Mul(Mul(two, x), h)), one)),
                                Mul(Square(fidelityDen), shiftedDen))))),
                    "The formula compares the secant at nonzero finite increment h with the linear jet coefficient at x. Both fidelity denominators are positive for finite rational inputs."),
                Law("formal-leibniz", "deriv_mul_equivAt", "Leibniz's rule through every degree",
                    All(["N"], naturals, All(["f", "g"], coefficients,
                        EquivAt(n, Deriv(Mul(f, g)), Add(Mul(Deriv(f), g), Mul(f, Deriv(g)))))),
                    "Equivalence through degree N requires agreement at every coefficient from zero to N inclusive. The derivative at degree N reads the coefficient in degree N + 1."),
                Law("formal-exp-derivative", "deriv_exp", "The exponential differential equation",
                    All(["a"], scalar, Equiv(Deriv(ExpAt(a)), Mul(a, ExpAt(a)))),
                    "The coefficient at degree n is a to the power n divided by n factorial. Setting a to one gives the unit-rate exponential equation."),
                Law("formal-cos-derivative", "deriv_cos", "The cosine differential equation",
                    Equiv(Deriv(cos), Negative(sin)),
                    "The cosine coefficients in even degree 2n are the alternating signs divided by (2n) factorial. The odd coefficients vanish."),
                Law("formal-sin-derivative", "deriv_sin", "The sine differential equation",
                    Equiv(Deriv(sin), cos),
                    "The sine coefficients in odd degree 2n + 1 are the alternating signs divided by (2n + 1) factorial. The even coefficients vanish."),
                Law("formal-exp-addition", "exp_add", "The exponential addition law",
                    All(["a", "b"], scalar, Equiv(Mul(ExpAt(a), ExpAt(b)), ExpAt(Add(a, b)))),
                    "Leibniz's rule gives the rate a + b for the product. Its constant coefficient is one, which fixes the solution coefficient by coefficient."),
                Law("formal-exp-inverse", "exp_inverse", "The formal exponential inverse",
                    All(["a"], scalar, If(Finite(a), Equiv(Mul(ExpAt(a), ExpAt(Negative(a))), one))),
                    "For a finite parameter, adding its negative gives the zero rate. The formal exponential at the zero rate is the constant series one."),
                Law("formal-pythagorean", "cos_sq_add_sin_sq", "The formal Pythagorean identity",
                    Equiv(Add(Square(cos), Square(sin)), one),
                    "The derivative of the sum of the two squares vanishes by Leibniz's rule and the two trigonometric differential equations. The constant coefficient is one."),
                Law("formal-atan-ode", "atan_ode", "The arctangent differential equation",
                    Equiv(Mul(Deriv(atan), denominator), one),
                    "In degree 2n + 1, arctangent has the alternating sign divided by 2n + 1. The even coefficients vanish. After differentiation the alternating even powers cancel against their two-degree shift."),
                Law("formal-cayley-cos-ode", "cayley_cos_ode", "The Cayley cosine differential equation",
                    Equiv(Mul(Deriv(cayleyCos), denominator), Mul(minusTwo, cayleySin)),
                    "The Cayley cosine is the formal rational function with numerator 1 - eta squared and denominator 1 + eta squared."),
                Law("formal-cayley-sin-ode", "cayley_sin_ode", "The Cayley sine differential equation",
                    Equiv(Mul(Deriv(cayleySin), denominator), Mul(two, cayleyCos)),
                    "The Cayley sine has numerator 2 eta and the same denominator as the Cayley cosine."),
                Law("formal-cayley-uniqueness", "cayley_unique_at", "The Cayley system determines each truncation",
                    All(["N"], naturals, All(["f", "g"], coefficients,
                        If(And(Equiv(Coeff(f, zero), one), Equiv(Coeff(g, zero), zero)),
                            If(And(firstCayleyEq, secondCayleyEq),
                                And(EquivAt(n, f, cayleyCos), EquivAt(n, g, cayleySin)))))),
                    "The streams start at (1, 0). The equations force their coefficients through degree N to be finite. At each degree k below N, the equations determine the next coefficients by division by k + 1. Consequently both streams agree with the Cayley pair through degree N, including degree zero."))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula All(string[] variables, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), type))], body);

    private static Formula Below(Formula naturals, Formula k, Formula n, Formula body) =>
        All(["k"], naturals, If(new Formula.Relation(k, FormulaRelationOperator.LessThan, n), body));

    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Div(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Negative(Formula value) => Seq(Minus, value);
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula Cube(Formula value) => new Formula.Power(value, D(3));
    private static Formula Tuple(Formula a, Formula b, Formula c) => Seq(Open, a, Comma, Sp, b, Comma, Sp, c, Close);
    private static Formula Coeff(Formula stream, Formula k) => Call("coeff", stream, k);
    private static Formula Deriv(Formula value) => Call("deriv", value);
    private static Formula ExpAt(Formula value) => Call("Exp", value);
    private static Formula Finite(Formula value) => Call("Finite", value);
    private static Formula Equiv(Formula left, Formula right) => Call("Equivalent", left, right);
    private static Formula EquivAt(Formula n, Formula left, Formula right) => Call("EquivalentAt", n, left, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula If(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static DocumentBlock.Describe Law(string id, string selector, string title, Formula statement, string commentary) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create($"{Module}.{selector}"),
            H(title),
            StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(commentary))),
            DescribeRole.Theorem);
}
