using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class ParityNodeDividedDifferenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/ParityNodeDividedDifference.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let z be distinct integer nodes indexed by a finite type, even on a set A of indices and odd off A, and let alpha = #A and beta = #A^c. If the binomial coefficient C(alpha + beta - 2, alpha - 1) is odd, then the partial divided-difference sum over the even nodes, the sum over i in A of 1 / prod_{j != i} (z i - z j), is a nonzero rational number of 2-adic valuation 0.",
        H("Divided differences over even and odd integer nodes are 2-adic units"),
        Blocks(
            Node("unit", "The even-node partial sum is a 2-adic unit", UnitFormula(),
                "Write the even nodes as z i = 2 mu i. The sum equals 2^(1 - alpha) times the divided difference, over the integer nodes mu, of g(2 mu) with g(x) = prod_{j not in A} 1 / (x - z j). In the 2-adic integers every z j with j not in A is a unit u_j^(-1), and 1 / (x - z j) agrees at the even nodes, modulo 2^N, with the truncated geometric series -u_j sum_{t < N} (u_j x)^t. The divided difference of mu^i over alpha distinct integer nodes is the coefficient of degree alpha - 1 of the remainder of X^i modulo the monic nodal polynomial: it is an integer, it vanishes for i < alpha - 1 and it equals 1 for i = alpha - 1. Choosing N larger than the 2-adic valuations of the nodal products, the sum is congruent modulo 2 to the coefficient of x^(alpha - 1) in prod_{j not in A} (-u_j sum_{t < N} (u_j x)^t). Modulo 2 this product is (1 + x + ... + x^(N-1))^beta, whose coefficient of degree alpha - 1 is C(alpha + beta - 2, alpha - 1). An odd coefficient makes the sum a 2-adic unit. The binomial index is written card(iota) - 2 with natural-number subtraction, which equals alpha + beta - 2 whenever alpha + beta >= 2; for a single node it is 0, matching the value 1 of the sum.",
                "evenOdd_dividedDifference_twoAdicUnit", DescribeRole.Theorem, AssessedProvenance.FromRepo())),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create("paritynode-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Inst(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Minus2(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula NotIn(Formula a, Formula s) => new Formula.Not(Parenthesized(Seq(a, Sp, InMacro, Sp, s)));

    private static Formula BigSum(Formula index, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(index, Sp, InMacro, Sp, set)), Sp, body);
    private static Formula BigProd(Formula index, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(index, Sp, InMacro, Sp, set)), Sp, body);

    private static Formula DividedSum(Formula z, Formula a)
    {
        Formula i = F.Id("i"), j = F.Id("j");
        Formula difference = Minus2(new Formula.Apply(z, [i]), new Formula.Apply(z, [j]));
        Formula nodal = BigProd(j, Call("erase", Named("univ"), i),
            Cast(Cast(difference, Integers()), Rationals()));
        return BigSum(i, a, new Formula.Power(Parenthesized(nodal), new Formula.Negate(D(1))));
    }

    private static Formula UnitFormula()
    {
        Formula iota = F.Id("iota"), z = F.Id("z"), a = F.Id("A"), i = F.Id("i");
        Formula sum = DividedSum(z, a);
        Formula conclusion = And(NotEqual(sum, D(0)), Equal(Call("padicValRat", D(2), sum), D(0)));
        Formula binomial = Call("Odd", Call("choose",
            Minus2(Call("card", iota), D(2)), Minus2(Call("card", a), D(1))));
        Formula oddOff = All("i", iota, Implies(NotIn(i, a), Call("Odd", new Formula.Apply(z, [i]))));
        Formula evenOn = All("i", a, Call("Even", new Formula.Apply(z, [i])));
        Formula body = All("A", Call("Finset", iota),
            Implies(Call("Nonempty", a), Implies(Parenthesized(evenOn), Implies(Parenthesized(oddOff),
                Implies(binomial, conclusion)))));
        Formula overNodes = All("z", Arrow(iota, Integers()), Implies(Call("Injective", z), body));
        return Disp(All("iota", F.Id("Type"),
            Inst(Call("Fintype", iota), Inst(Call("DecidableEq", iota), overNodes))));
    }
}
