using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Sun;

internal sealed class LegendreOddPowerTelescoperDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Sun/LegendreOddPowerTelescoper.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Analytic/cuisun2026legendre");
    private static readonly Formula Nat = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula Integers = Seq(Mathbb, Grp(F.Id("Z")));
    private static readonly Formula Rationals = Seq(Mathbb, Grp(F.Id("Q")));
    private static readonly Formula ZPoly = Call("Polynomial", Integers);
    private static readonly Formula QPoly = Call("Polynomial", Rationals);
    private static readonly Formula M = F.Id("m"), P = F.Id("p"), T = F.Id("t"), X = F.Id("X"), Family = F.Id("f");
    private static Formula FamilyType => new Formula.TypeArrow(Call("Fin", M), ZPoly);

    private const string PQuote = "The famous Legendre polynomials {P_n(x)} are given by P_0(x) = 1, P_1(x) = x and (n + 1)P_{n+1}(x) = (2n + 1)xP_n(x) − nP_{n−1}(x) (n ≥ 1).";
    private const string ConjectureQuote = "Suppose that m, p ∈ Z^+. Then there are integral polynomials f_i(t) with degree i (i = 0, 1, …, m − 1) such that (1 − x)^{m+1} Σ_{n=0}^{p−1} (2n + 1)^{2m+1} P_n(x) = pL_m(p, 1 − x)P_{p−1}(x) − pL_m(−p, 1 − x)P_p(x), where L_m(p, t) = (2p + 1)^{2m} t^m + f_{m−1}((2p + 1)^2) t^{m−1} + · · · + f_1((2p + 1)^2) t + f_0.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral coefficient polynomials provide telescopers for every positive odd-power Legendre sum.",
        H("Integral Legendre Odd-Power Telescopers"),
        Blocks(
            Paragraph(Text("The identity is an equality in Q[X], with X the indeterminate. "
                + "C embeds a rational number as a constant polynomial. rat and int cast naturals "
                + "to Q and Z; zrat casts integers to Q. val extracts a natural index from a Fin "
                + "element or an attached range element. range(p) contains the naturals below p, "
                + "and attach carries each such index with its membership proof. ltRange(i) extracts "
                + "the bound from that proof, and finMk (Fin.mk) inserts the index and bound. natSub is "
                + "natural subtraction truncated at zero. eval2 uses the indicated coefficient "
                + "homomorphism and evaluation point. intCastRingHom is Int.castRingHom. The lower coefficients are chosen once for "
                + "each m and then used for every p.")),
            Node("P", "The Legendre polynomials", PFormula(),
                "Equation (1.1), page 1: \"" + PQuote + "\" The definition solves this recurrence "
                + "in Q[X] at index n+1 for n at least one. Its successor form is displayed with "
                + "n starting at zero. The fraction is rational division, and its denominator is nonzero.", true),
            Node("L", "The source polynomial L", LFormula(),
                "Conjecture 2.1, page 10: \"" + ConjectureQuote + "\" L(m,f,p,t) is the displayed "
                + "L_m(p,t) with the coefficient family f made explicit. The constant coefficient "
                + "is f(0), an integer constant polynomial. The sum uses the attached range below m "
                + "and evaluates every lower coefficient at the same square (2p+1)^2. The parameter "
                + "p is an integer, so the negative endpoint is part of the same definition.", true),
            Node("claim", "Cui-Sun Conjecture 2.1", IffF(F.Id("claim"), ClaimFormula()),
                "Conjecture 2.1, page 10: \"" + ConjectureQuote + "\" The encoding quantifies m and p "
                + "over positive naturals and places the existential coefficient family before the "
                + "quantifier over p. Every coefficient lies in Z[X], is nonzero, and has natural "
                + "degree equal to its index. This includes the nonzero degree-zero coefficient. "
                + "The indeterminate is X; no restriction or division by 1-X is imposed.", true),
            Node("result", "The identity for every m", ClaimFormula(),
                "A degree-lowering integer operator produces the coefficient family. Binomial "
                + "expansion identifies its evaluation with a symmetric difference at r+2 and r-2. "
                + "Its iterates on the monomial of degree m are nonzero of successive degrees "
                + "m,m-1,...,0 and then vanish. Alternating these iterates gives a finite inverse "
                + "for multiplication by t plus the operator. The Legendre recurrence turns this "
                + "inverse identity into a boundary difference, and induction sums the differences "
                + "over all indices below p.", false, DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        bool literature, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create("cui-sun-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Apply(Formula fun, Formula arg) => new Formula.Apply(fun, [arg]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula EqF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula AndF(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula ImpF(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula SumOver(Formula index, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(index, Sp, InMacro, Sp, domain)), Sp, Parenthesized(body));
    private static Formula C(Formula q) => Call("C", q);
    private static Formula Odd(Formula n) => Add(Mul(D(2), n), D(1));

    private static Formula PFormula()
    {
        var n = F.Id("n");
        var next = Add(n, D(1));
        var numerator = Sub(Mul(Mul(C(Call("rat", Odd(next))), X), Call("P", next)),
            Mul(C(Call("rat", next)), Call("P", n)));
        var reciprocal = C(new Formula.Fraction(D(1), Call("rat", Add(n, D(2)))));
        return AndF(EqF(Call("P", D(0)), D(1)), AndF(EqF(Call("P", D(1)), X),
            All("n", Nat, EqF(Call("P", Add(n, D(2))), Mul(numerator, reciprocal)))));
    }

    private static Formula LFormula()
    {
        var i = F.Id("i");
        var label = Call("val", i);
        var point = Call("zrat", Odd(P));
        var coeff = Apply(Family, Call("finMk", label, Call("ltRange", i)));
        var lower = SumOver(i, Call("attach", Call("range", M)),
            Mul(C(Call("eval2", Call("intCastRingHom", Rationals), Power(point, D(2)), coeff)), Power(T, label)));
        return All("m", Nat, All("f", FamilyType, All("p", Integers, All("t", QPoly,
            EqF(Call("L", M, Family, P, T),
                Add(Mul(C(Power(point, Mul(D(2), M))), Power(T, M)), lower))))));
    }

    private static Formula ClaimFormula()
    {
        var i = F.Id("i");
        var n = F.Id("n");
        var degree = All("i", Call("Fin", M),
            AndF(EqF(Call("natDegree", Apply(Family, i)), Call("val", i)), NeF(Apply(Family, i), D(0))));
        var t = Sub(D(1), X);
        var sum = SumOver(n, Call("range", P), Mul(Power(C(Call("rat", Odd(n))), Odd(M)), Call("P", n)));
        var lhs = Mul(Power(t, Add(M, D(1))), sum);
        var rhs = Sub(Mul(Mul(C(Call("rat", P)), Call("L", M, Family, Call("int", P), t)),
                Call("P", Call("natSub", P, D(1)))),
            Mul(Mul(C(Call("rat", P)), Call("L", M, Family, new Formula.Negate(Call("int", P)), t)), Call("P", P)));
        return All("m", Nat, ImpF(LeF(D(1), M), Some("f", FamilyType,
            AndF(degree, All("p", Nat, ImpF(LeF(D(1), P), EqF(lhs, rhs)))))));
    }
}
