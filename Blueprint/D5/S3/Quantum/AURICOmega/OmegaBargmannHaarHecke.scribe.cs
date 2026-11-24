using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class OmegaBargmannHaarHeckeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/AURICOmega/OmegaBargmannHaarHecke";

    public DocumentDefinition Create()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c"), k = F.Id("k");
        Formula psi = F.Id("s"), rotor = F.Id("A"), p = F.Id("p");
        Formula q = F.Id("q"), u = F.Id("u"), v = F.Id("v");
        Formula zero = D(0), one = D(1), two = D(2), five = D(5);
        Formula quadruples = new Formula.Power(Integers, D(4));
        Formula triad = Call("triad", b, a, b);
        Formula nonzeroPair = And(Ne(a, zero), Ne(b, zero));
        Formula doubled = Sub(Mul(two, Call("kappa", a, b)), one);
        Formula eigenvalue = new Formula.Fraction(Seq(Minus, D(2)), five);
        Formula margin = new Formula.Fraction(D(4, 9, 6), D(2, 5));
        Formula xy = F.Id("XY"), yx = F.Id("YX"), unwindY = F.Id("U"), x = F.Id("X");
        Formula product = Call("mul", psi, rotor);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Exact projective quaternion geometry, even moments on the three-sphere, and quaternion divisibility.",
            H("Rational quaternion geometry and harmonics"),
            Blocks(
                Law("gram-determinant-nonnegative", "detGram3_nonneg",
                    "The normalized Gram determinant is nonnegative",
                    All(If(And(nonzeroPair, Ne(c, zero)), Le(zero, Call("detGram", a, b, c))),
                        ("a", quadruples), ("b", quadruples), ("c", quadruples)),
                    "Clearing the positive product of squared norms gives the sum of the squares of the four maximal minors of the three coordinate rows."),
                Law("geodesic-doubling-gram-zero", "geodesic_doubling_detGram3_zero",
                    "The doubled ray has zero Gram determinant",
                    All(If(nonzeroPair, Equiv(Call("detGram", a, b, triad), zero)),
                        ("a", quadruples), ("b", quadruples)),
                    "The triad is twice the dot product times the second input minus its squared norm times the first input. Its squared norm is the first squared norm times the square of the second squared norm."),
                Law("geodesic-doubling-fidelity", "geodesic_doubling_kappa",
                    "Fidelity under great-circle doubling",
                    All(If(nonzeroPair, Equiv(Call("kappa", a, triad), Square(doubled))),
                        ("a", quadruples), ("b", quadruples)),
                    "Squaring the dot product with the triad gives the numerator. The denominator is the square of the original product of squared norms."),
                Law("haar-moment-recurrence", "haarKappaMoment_succ",
                    "Consecutive even scalar-coordinate Haar moments",
                    All(Equiv(Call("moment", Add(k, one)),
                        Mul(Call("moment", k), new Formula.Fraction(Add(Mul(two, k), one),
                            Mul(two, Add(k, two))))), ("k", Naturals)),
                    "The factorial functional evaluates the even monomials of the normalized three-sphere. Cancelling the shared factorials and powers of four gives the recurrence for every natural degree."),
                Law("three-character-orthonormality", "peter_weyl_chi012_orthonormal",
                    "The first three even characters are orthonormal",
                    Disp(And(Inner(0, 0, one), And(Inner(0, 1, zero), And(Inner(0, 2, zero),
                        And(Inner(1, 1, one), And(Inner(1, 2, zero), Inner(2, 2, one))))))),
                    "The characters have coefficient lists (1), (−1, 4), and (1, −12, 16). Convolving the coefficients and applying moments of degrees zero through four gives these six entries. Convolution is symmetric in the two factors."),
                Law("norm-five-hecke-eigenvalue", "heckeT5_chi1_eigenvalue",
                    "The six-spinor Hecke sum has eigenvalue negative two fifths",
                    All(If(Ne(q, zero), Equiv(Call("hecke", q), Mul(eigenvalue, Call("character", q)))),
                        ("q", quadruples)),
                    "The six right products each have five times the original squared norm. Pairing the opposite coordinate signs cancels the mixed terms in the squared scalar parts. The operator uses the unnormalized sum."),
                Law("norm-five-ramanujan-margin", "heckeT5_ramanujan_margin",
                    "The rational eigenvalue has positive Ramanujan margin",
                    Disp(And(Equiv(Sub(Mul(D(4), five), Square(eigenvalue)), margin), Lt(zero, margin))),
                    "Subtracting the squared eigenvalue from four times five gives 496 over 25."),
                Law("quaternion-gate-determinism", "quaternion_fractran_deterministic",
                    "Quaternion division by a nonzero integer is deterministic",
                    All(If(And(Ne(p, zero), And(Eq(product, Call("scale", p, u)),
                        Eq(product, Call("scale", p, v)))), Eq(u, v)),
                        ("s", quadruples), ("A", quadruples), ("u", quadruples), ("v", quadruples), ("p", Integers)),
                    "The transition equations give the same integer scaling of the two proposed outputs. Cancelling the nonzero factor in each coordinate identifies the outputs."),
                Law("quaternion-gate-order-separation", "quaternion_fractran_order_separation",
                    "The Y-unwind gate distinguishes equal-norm ordered products",
                    Disp(And(Eq(Call("normSq", xy), D(2, 5)),
                        And(Eq(Call("normSq", yx), D(2, 5)),
                            And(Eq(Call("mul", xy, unwindY), Call("scale", five, x)),
                                Seq(Neg, Sp, Open, new Formula.Bind(FormulaQuantifier.Exists,
                                    FormulaIdentifier.Create("q"), quadruples,
                                    Eq(Call("mul", yx, unwindY), Call("scale", five, q))), Close))))),
                    "The ordered states are (1, 2, 2, 4) and (1, 2, 2, −4). The unwind rotor is (1, 0, −2, 0) and the successful quotient is (1, 2, 0, 0). The reversed product has second coordinate −6, which has no integral quotient by five."))));
    }

    private static Formula Integers => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula All(Formula body, params (string Name, Formula Type)[] variables) =>
        Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(v => new Formula.BoundVariable(FormulaIdentifier.Create(v.Name), v.Type))], body));

    private static Formula Inner(byte a, byte b, Formula value) => Equiv(Call("inner",
        new Formula.Subscript(F.Id("chi"), D(a)), new Formula.Subscript(F.Id("chi"), D(b))), value);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula Equiv(Formula a, Formula b) => Call("Equivalent", a, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula If(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);

    private static DocumentBlock.Describe Law(string id, string selector, string title, Formula statement, string explanation) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create($"{Module}.{selector}"), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);
}
