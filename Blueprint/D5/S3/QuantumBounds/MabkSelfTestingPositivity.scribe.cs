using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class MabkSelfTestingPositivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/MabkSelfTestingPositivity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/cao2026sizeindependent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The five-term MABK self-testing expression is nonnegative throughout the real cube for every n >= 6 and either of the two small index blocks h = 1, 2.",
        H("MABK self-testing positivity for the two remaining blocks"),
        Blocks(
            Node("kappa", "The cube endpoint", Disp(Equal(F.Id("kappa"),
                Sub(D(1), Div(D(1), RootTwo())))),
                "The endpoint is kappa = 1 - 1/sqrt(2), as in the Supplemental Material. All divisions in this document are real divisions.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("lambdaA", "The source expression", LambdaFormula(),
                "The five terms are the displayed lambda expression in the Supplemental Material, Efficient Verification of Optimal Lower Bound, PDF p. 37. The source indices 1,...,n are encoded by Fin n through i -> i + 1. T is the source block T_a, and its complement T^c is the block P_a. Every product is a finite product over its displayed index set; v is real-valued. Lean's real square root is total and returns zero on negative arguments; the radicands are nonnegative on the stated cube.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectured non-negativity", ClaimFormula(),
                "The Supplemental Material, PDF p. 39, states verbatim: “For n ≤ 5 this bound is already established analytically [20, 23]; for n ≥ 6 the two remaining cases (h = 1, 2) are an open conjecture supported by the numerical evidence above.” The encoded assertion is non-negativity of the displayed lambda expression at every point of [0,kappa]^n. The condition h <= d holds automatically for n >= 6 and h in {1,2}; h = card(T) and d = card(T^c).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Positivity on the whole cube", Disp(F.Id("claim")),
                "Write r = sqrt(2), x_i = 1 - v_i, y_i = sqrt(2 v_i - v_i^2), a_i = 1 - ((1+r)/r)v_i and b_i = ((1+r)/r)v_i. The coordinate bounds give a_i >= x_i^2, b_i <= 1/2, y_i^2 <= 1/2 and x_i^2+y_i^2=1. For the complementary block J, let q be the product of x_i, d = card(J), B = product_T b_i, Y = product_T y_i and s = 1+r. A finite-product induction gives (product_J y_i)^2 <= (1-q^2) 2^{1-d}. Set K=(2+r)BY, C=1-K/2-s^2 2^{1-d} and F=1-s^2 Y^2+rB+K. Keeping the positive cubic term and using 2q^3 >= 3q^2-1 gives the lower bound C(1-q^2)+Fq^2. For h=1, F is nonnegative by factorization on the unit circle; the certificate is the denominator-cleared version of the factorization with t=y/(1+x). For h=2, F is bounded below by 1-(5/2+13r/8)Y^2+(5/4+7r/8)Y^3 for 0 <= Y <= 1/2, which is at least (34-19r)/64 > 0. The block-size bounds make C nonnegative in both cases. This proves the scalar conjecture; the Bell-operator reductions and the extractability conclusions of the source are outside this module.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("mabk-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) => Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula LessEq(Formula left, Formula right) => Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Div(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Square(Formula value) => new Formula.Power(Parenthesized(value), D(2));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Root(Formula value) => Seq(Sqrt, Grp(value));
    private static Formula RootTwo() => Root(D(2));
    private static Formula Coefficient() => Div(Add(D(1), RootTwo()), RootTwo());
    private static Formula Complement(Formula set) => new Formula.Power(set, Seq(Mathrm, Grp(F.Id("c"))));
    private static Formula Product(Formula set, Formula value) => Seq(Prod, Underscore,
        Grp(F.Id("j"), Sp, InMacro, Sp, set), Sp, Parenthesized(value));

    private static Formula LambdaFormula()
    {
        Formula n = F.Id("n"), t = F.Id("T"), v = F.Id("v"), j = F.Id("j");
        Formula fin = Call("Fin", n), comp = Complement(t), vi = Call("v", j);
        Formula c = Coefficient(), a = Sub(D(1), Mul(c, vi)), b = Mul(c, vi);
        Formula x = Sub(D(1), vi), z = Mul(vi, Sub(D(2), vi));
        Formula y = Root(Sub(Mul(D(2), vi), Square(vi)));
        Formula first = Mul(new Formula.Power(Parenthesized(c), n), Product(fin, Mul(vi, a)));
        Formula second = Mul(RootTwo(), Parenthesized(Add(
            Mul(Product(t, a), Product(comp, b)), Mul(Product(t, b), Product(comp, a)))));
        Formula third = Mul(Square(Add(RootTwo(), D(1))), Parenthesized(Add(
            Mul(Product(t, Square(x)), Product(comp, z)), Mul(Product(t, z), Product(comp, Square(x))))));
        Formula fourth = Mul(Parenthesized(Add(D(2), RootTwo())), Parenthesized(Add(
            Mul(Product(t, Mul(a, x)), Product(comp, Mul(b, y))),
            Mul(Product(t, Mul(b, y)), Product(comp, Mul(a, x))))));
        Formula expr = Add(Sub(Add(Add(D(1), first), second), third), fourth);
        return Disp(All("n", Nats(), All("T", Call("Finset", fin),
            All("v", Seq(fin, To, Reals()), Equal(Call("lambdaA", n, t, v), expr)))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), t = F.Id("T"), v = F.Id("v"), i = F.Id("i");
        Formula fin = Call("Fin", n);
        Formula sizes = Logic(Equal(Call("card", t), D(1)), FormulaLogicOperator.Or,
            Equal(Call("card", t), D(2)));
        Formula cube = All("i", fin, Logic(LessEq(D(0), Call("v", i)), FormulaLogicOperator.And,
            LessEq(Call("v", i), F.Id("kappa"))));
        Formula assertion = All("n", Nats(), Logic(LessEq(D(6), n), FormulaLogicOperator.Implies,
            All("T", Call("Finset", fin), Logic(sizes, FormulaLogicOperator.Implies,
                All("v", Seq(fin, To, Reals()), Logic(cube, FormulaLogicOperator.Implies,
                    LessEq(D(0), Call("lambdaA", n, t, v))))))));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff, assertion));
    }
}
