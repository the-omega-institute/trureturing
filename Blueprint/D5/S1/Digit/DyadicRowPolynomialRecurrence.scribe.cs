using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class DyadicRowPolynomialRecurrenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula p = F.Id("P"), z = F.Id("Q"), n = F.Id("n"), m = F.Id("m");
        Formula k = F.Id("k"), q = F.Id("q"), r = F.Id("r"), x = F.Id("X");
        Formula w = Call("wt", k);
        Formula twoK = Mul(D(2), k);
        Formula row = Call("R", n);
        Formula half = Call("div", n, D(2));
        Formula v = Call("padicValNat", D(2), n);
        Formula index = Sub(Mul(Pow(D(2), Add(m, D(1))), Parenthesized(Add(twoK, D(1)))), D(2));
        Formula operatorBody = Mul(x, Parenthesized(Sub(Call("comp", p, Add(x, D(1))), p)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Dyadic row recurrence and Pascal accumulator identities for OEIS A373183.",
            H("Dyadic Row Polynomials and Their Pascal Accumulator"),
            Blocks(
                Node("D", "difference-operator", "Polynomial difference operator",
                    All(p, Polynomials(), Equal(Call("D", p), operatorBody)),
                    "D maps integer polynomials to integer polynomials. X is the polynomial "
                    + "indeterminate, comp(P,Q) means polynomial composition P(Q), and 1 is "
                    + "the constant integer polynomial. All polynomial identities below are in Z[X].",
                    AssessedProvenance.FromRepo(),
                    DescribeRole.Definition),
                Node("D_add", "difference-additivity", "Additivity",
                    All(Seq(p, Comma, Sp, z), Polynomials(),
                        Equal(Call("D", Add(p, z)), Add(Call("D", p), Call("D", z)))),
                    "The defining difference distributes over addition. This companion is used "
                    + "by both induction arguments.",
                    AssessedProvenance.FromRepo()),
                Node("D_X", "difference-indeterminate", "The zero-index boundary identity",
                    Equal(Call("D", x), x),
                    "This identity supplies the boundary at row zero in the even recurrence.",
                    AssessedProvenance.FromRepo()),
                Node("D_X_mul", "difference-commutator", "Multiplication by the indeterminate",
                    All(p, Polynomials(), Equal(Call("D", Mul(x, p)),
                        Add(Mul(x, p), Mul(Parenthesized(Add(x, D(1))), Call("D", p))))),
                    "The commutator is the odd-index step of the valuation descent and the "
                    + "polynomial form of the accumulator's Pascal step.",
                    AssessedProvenance.FromRepo()),
                Node("R", "row-polynomial", "The independent dyadic row recursion",
                    All(n, Naturals(), Equal(row,
                        Call("ite", Equal(n, D(0)), x,
                            Call("ite", Equal(Call("mod", n, D(2)), D(0)),
                                Call("D", Call("R", half)), Mul(x, Call("R", half)))))),
                    "R : N -> Z[X] is defined by this well-founded recursion on n. "
                    + "div(n,2) denotes natural-number integer division, and mod(n,2) denotes "
                    + "the remainder. ite(c,a,b) returns a when c holds and b otherwise. "
                    + "The recurrence is transcribed from OEIS A373183 (Kurkov, 2024); "
                    + "Conjectures 1 and 9 are stated there as conjectures; the proofs are this repository's.",
                    AssessedProvenance.FromRepo(),
                    DescribeRole.Definition),
                Node("R_zero", "row-zero", "Initial row",
                    Equal(Call("R", D(0)), x),
                    "The initial polynomial is X.",
                    AssessedProvenance.FromRepo()),
                Node("R_odd", "row-odd", "Odd rows",
                    All(n, Naturals(), Equal(Call("R", Add(Mul(D(2), n), D(1))), Mul(x, row))),
                    "The odd-row clause holds for every natural n, including zero.",
                    AssessedProvenance.FromRepo()),
                Node("R_even", "row-even", "Even rows",
                    All(n, Naturals(), Equal(Call("R", Mul(D(2), n)),
                        Mul(x, Parenthesized(Sub(Call("comp", row, Add(x, D(1))), row))))),
                    "For positive n this recurrence is transcribed from OEIS A373183 (Kurkov, 2024) "
                    + "as scope-matched context. The Lean statement is a repository strengthening to all n; "
                    + "the n=0 clause follows from R_zero and the definition of D. Conjectures 1 and 9 "
                    + "are stated there as conjectures; the proofs are this repository's.",
                    AssessedProvenance.FromRepo()),
                Node("conjecture1", "dyadic-row-recurrence", "The valuation recurrence",
                    All(n, Naturals(), ImpliesFormula(Less(D(0), n),
                        Equal(Call("R", Mul(D(2), n)),
                            Add(Add(row, Call("R", Sub(n, Pow(D(2), v)))),
                                Call("R", Sub(Mul(D(2), n), Pow(D(2), v))))))),
                    "This is Conjecture 1 from OEIS A373183 (Kurkov, 2024), where it is stated "
                    + "as a conjecture; its proof is this repository's. "
                    + "For positive n, padicValNat(2,n) is v_2(n), the exponent of 2 dividing n. "
                    + "Both subtractions n-2^v and 2n-2^v are truncated natural-number subtraction. "
                    + "Strong induction descends along the binary recursion: the even case applies "
                    + "D to the lower-index identity, and the odd case uses the commutator.",
                    AssessedProvenance.FromRepo()),
                Node("wt", "binary-weight", "Binary weight",
                    All(n, Naturals(), Equal(Call("wt", n), Call("sum", Call("digits", D(2), n)))),
                    "wt : N -> N is the sum of Mathlib's Nat.digits 2 n, the list of binary "
                    + "digits in least-significant-first order; digits(2,0) is empty.",
                    AssessedProvenance.FromRepo(),
                    DescribeRole.Definition),
                Node("R_coeff_zero", "even-row-zero-coefficient", "Even rows have zero constant coefficient",
                    All(k, Naturals(), Equal(Call("coeff", Call("R", twoK), D(0)), D(0))),
                    "For P=R(2k), this is the atom-named identity P(0)=0, expressed as its "
                    + "constant coefficient. The proof is this repository's.",
                    AssessedProvenance.FromRepo()),
                Node("R_degree", "even-row-degree-bound", "Even-row degree bound",
                    All(k, Naturals(), LessEqual(Call("natDegree", Call("R", twoK)), Add(w, D(1)))),
                    "For P=R(2k) and d=wt(k)+1, this is the atom-named bound deg(P)<=d. "
                    + "The proof is this repository's.",
                    AssessedProvenance.FromRepo()),
                Node("T", "row-coefficient", "Triangle coefficients",
                    All(Seq(n, Comma, Sp, q), Naturals(), Equal(Call("T", n, q), Call("coeff", row, q))),
                    "T : N -> N -> Z is defined by T(n,q)=(R(n)).coeff(q). Thus T(n,q) "
                    + "is the integer coefficient of X^q, including the zero coefficient q=0.",
                    AssessedProvenance.FromRepo(),
                    DescribeRole.Definition),
                Node("e", "pascal-accumulator", "The independent coefficient accumulator",
                    AccumulatorDefinition(),
                    "e : N -> N -> N -> Z is defined independently by these clauses, not by "
                    + "the target row formula. ite(c,a,b) means if c then a else b. Support "
                    + "takes priority outside 1<=q<=r. Every subtraction in q-1 and "
                    + "wt(k)+q+1-(r+2) is truncated natural-number subtraction. This is the "
                    + "accumulator transcribed from OEIS A373183 (Kurkov, 2024) as part of "
                    + "Conjecture 9; Conjectures 1 and 9 are stated there as conjectures; the proofs "
                    + "are this repository's.",
                    AssessedProvenance.FromRepo(),
                    DescribeRole.Definition),
                Node("e_support", "accumulator-support", "Support interval",
                    All(Seq(r, Comma, Sp, k, Comma, Sp, q), Naturals(),
                        ImpliesFormula(Seq(Equal(q, D(0)), Sp, Lor, Sp, Less(r, q)),
                            Equal(Call("e", r, k, q), D(0)))),
                    "The accumulator is zero at q=0 and above row r, equivalently outside [1,r].",
                    AssessedProvenance.FromRepo()),
                Node("e_one", "accumulator-initial", "Initial accumulator entry",
                    All(k, Naturals(), Equal(Call("e", D(1), k, D(1)), Call("T", twoK, Add(w, D(1))))),
                    "The sole supported entry at r=1 is the source coefficient T(2k,wt(k)+1).",
                    AssessedProvenance.FromRepo()),
                Node("e_recurrence", "accumulator-step", "Pascal recurrence on the support",
                    All(Seq(r, Comma, Sp, k, Comma, Sp, q), Naturals(),
                        ImpliesFormula(AtLeastTwoAndSupported(r, q),
                            Equal(Call("e", r, k, q), AccumulatorStep(r, k, q)))),
                    "For r>=2 and 1<=q<=r the two previous entries are supplemented by "
                    + "T(2k,wt(k)+q+1-r) when r<=wt(k)+q, and zero otherwise. The guard is "
                    + "equivalent to the source's integer inequality r-q<=wt(k). All subtractions "
                    + "r-1, q-1 and wt(k)+q+1-r in this display are natural-number subtraction.",
                    AssessedProvenance.FromRepo()),
                Node("R_factorization", "row-factorization", "Independent binary row factorization",
                    All(Seq(m, Comma, Sp, k), Naturals(), Equal(Call("R", index),
                        Call("D", Mul(Pow(x, m), Call("R", twoK))))),
                    "Induction through the odd-row clause gives the binary tail, then the even "
                    + "clause gives this factorization. The subtraction of 2 in the row index "
                    + "is natural-number subtraction.",
                    AssessedProvenance.FromRepo()),
                Node("E", "accumulator-polynomial", "Accumulator polynomial",
                    All(Seq(r, Comma, Sp, k), Naturals(), Equal(Call("E", r, k),
                        Seq(new Formula.Subscript(Sum, new Formula.Relation(q, FormulaRelationOperator.MemberOf,
                                Call("range", Add(r, D(1))))),
                            Sp, Call("monomial", q, Call("e", r, k, q))))),
                    "E : N -> N -> Z[X] is the finite sum over q in Finset.range(r+1), "
                    + "that is 0<=q<=r. monomial(q,a) is the integer polynomial a*X^q; "
                    + "this explicitly embeds the integer coefficient e(r,k,q) into Z[X].",
                    AssessedProvenance.FromRepo(),
                    DescribeRole.Definition),
                Node("E_after_degree", "accumulator-after-degree", "Accumulator after the degree bound",
                    All(Seq(m, Comma, Sp, k), Naturals(),
                        Equal(Call("E", Add(Add(w, D(1)), m), k),
                            Call("D", Mul(Pow(x, m), Call("R", twoK))))),
                    "Put P=R(2k) and d=wt(k)+1. The proof derives P.coeff(0)=0 and "
                    + "natDegree(P)<=d, identifies the accumulator with D of a truncated "
                    + "Horner polynomial, recovers P at d, and obtains X^m*P at d+m. "
                    + "In particular m=0 gives E(d,k)=D(P).",
                    AssessedProvenance.FromRepo()),
                Node("conjecture9", "pascal-coefficient-identity", "The Pascal accumulator identity",
                    All(Seq(m, Comma, Sp, k, Comma, Sp, q), Naturals(),
                        ImpliesFormula(Less(D(0), q), Equal(Call("T", index, q),
                            Call("e", Add(Add(m, w), D(1)), k, q)))),
                    "This is Conjecture 9 from OEIS A373183 (Kurkov, 2024), where it is stated "
                    + "as a conjecture; its proof is this repository's. "
                    + "The subtraction of 2 in the row index is natural-number subtraction. "
                    + "Coefficient extraction from the row factorization and accumulator identity "
                    + "proves the whole statement. This proof is independent of conjecture1; "
                    + "both proofs share D_add, D_X and D_X_mul.",
                    AssessedProvenance.FromRepo()))));
    }

    private static Formula AccumulatorDefinition()
    {
        Formula r = F.Id("r"), k = F.Id("k"), q = F.Id("q");
        Formula next = Add(r, D(2));
        Formula first = All(Seq(k, Comma, Sp, q), Naturals(), Equal(Call("e", D(0), k, q), D(0)));
        Formula initial = All(Seq(k, Comma, Sp, q), Naturals(),
            Equal(Call("e", D(1), k, q), Call("ite", Equal(q, D(1)),
                Call("T", Mul(D(2), k), Add(Call("wt", k), D(1))), D(0))));
        Formula step = All(Seq(r, Comma, Sp, k, Comma, Sp, q), Naturals(),
            Equal(Call("e", next, k, q), Call("ite", Supported(next, q),
                AccumulatorStep(next, k, q, Add(r, D(1))), D(0))));
        return new Formula.Aligned([Parenthesized(first), Parenthesized(initial), Parenthesized(step)]);
    }

    private static Formula AccumulatorStep(Formula r, Formula k, Formula q, Formula? previous = null) =>
        Add(Add(Call("e", previous ?? Sub(r, D(1)), k, q),
                Call("e", previous ?? Sub(r, D(1)), k, Sub(q, D(1)))),
            Call("ite", LessEqual(r, Add(Call("wt", k), q)),
                Call("T", Mul(D(2), k), Sub(Add(Add(Call("wt", k), q), D(1)), r)), D(0)));

    private static Formula AtLeastTwoAndSupported(Formula r, Formula q) =>
        Seq(LessEqual(D(2), r), Sp, Land, Sp, Parenthesized(Supported(r, q)));
    private static Formula Supported(Formula r, Formula q) =>
        Seq(Less(D(0), q), Sp, Land, Sp, LessEqual(q, r));

    private static DocumentBlock Node(string name, string id, string title, Formula formula,
        string prose, AssessedProvenance provenance,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create("D5/S1/Digit/DyadicRowPolynomialRecurrence." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(DefinitionDsl.Text(prose))), role);

    private static Formula All(Formula variables, Formula domain, Formula body) =>
        Seq(Forall, Sp, variables, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Less(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula LessEqual(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula ImpliesFormula(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Implies, Sp, b);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Polynomials() => Seq(Mathbb, Grp(F.Id("Z")), OpenBracket, F.Id("X"), CloseBracket);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula>();
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        return Seq(Operatorname, Grp(F.Id(name)), Parenthesized(Seq([.. items])));
    }
}
