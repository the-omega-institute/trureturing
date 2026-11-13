using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.RepeatingDecimal;

internal sealed class RepeatingDecimalQuotientDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Arith/RepeatingDecimal/RepeatingDecimalQuotient.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/weisstein2026repeatingdecimal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer long division realizes rational values and prescribed periods.",
        H("Long division, infinite positional values, and period quotients"),
        Blocks(
            Entry("long-division-remainder", "remainder", "Recursive remainder", RemainderFormula(),
                "For natural b, p, q, start with r(0)=p and repeatedly multiply by b and take "
                + "the remainder modulo q. The definition is total, including q=0.", false),
            Entry("long-division-digit", "digit", "Quotient digit", DigitFormula(),
                "The digit at position n is natural division of b times the current remainder by q. "
                + "Under b>1 and p<q, every remainder is less than q and every digit is less than b. "
                + "The latter bound supplies Mathlib's finite digit alphabet in the summability proof.", false),
            Entry("long-division-prefix", "longDivisionPrefix", "Positional integer prefix", PrefixFormula(),
                "P(0)=0 and P(n+1)=b P(n)+d(n). Thus the first generated digit is the most "
                + "significant digit of the n-digit integer prefix; leading zeroes are allowed.", false),
            Entry("long-division-invariant", "long_division_invariant", "Conserved scaled numerator",
                InvariantFormula(),
                "For every natural b,p,q,n, including zero base or denominator, the recursive "
                + "state satisfies q P(n)+r(n)=b^n p. The proof inducts on n and uses the "
                + "Euclidean division identity at each step. Neither the prefix nor the remainder "
                + "is defined by the claimed closed form.", true),
            Entry("long-division-value", "long_division_value", "The infinite positional value",
                ValueFormula(),
                "For every natural base b>1 and p<q, the digit series has sum p/q in the reals, "
                + "and P(n)/b^n tends to p/q as n tends to infinity. Natural p<q implies q>0. "
                + "The prefix-to-partial-sum induction and conserved numerator express the error "
                + "as r(n)/(q b^n), bounded by b^(-n). Mathlib supplies geometric convergence and "
                + "summability of finite-alphabet positional digits. This proves infinite-series "
                + "semantics for the actual recursively generated digits.", true),
            Entry("long-division-period", "long_division_period", "Prescribed period and block quotient",
                PeriodFormula(),
                "For b>1, p<q and any natural L with q dividing b^L-1, the digit at n+L equals "
                + "the digit at n for every natural n, and (b^L-1)(p/q)=P(L) over the reals. "
                + "The invariant first gives r(L)=p; induction propagates this return through "
                + "the actual remainder recurrence. L=0 gives the trivial period and zero shift. "
                + "For L>0 the positive shift factor gives p/q=P(L)/(b^L-1). The period need "
                + "not be minimal, and no converse classification is asserted.", true),
            Paragraph(Text("Chapter 36's repeating-decimal example uses b=10, p=1, q=7, L=6. "
                + "Long division generates 1,4,2,8,5,7, with P(6)=142857; 7 divides 10^6-1. "
                + "Periodicity and the first six digits identify the infinite stream as "
                + "0.overline{142857}; its convergent series is 1/7. The block identity is "
                + "10^6 x-x=142857, hence x=142857/999999=1/7. This application is exposition, "
                + "with a transient compiled specialization, and introduces no finite-certificate theorem.")),
            Paragraph(Text("These are classical long-division and repeating-decimal facts. "
                + "The cited MathWorld entry attests the classical context; the arbitrary-base "
                + "integer-state-to-real-series connection is the formal bridge proved here. "
                + "No novelty claim or statement about the chapter's philosophical parable follows.")))));

    private static DocumentBlock.Describe Entry(string id, string decl, string title, Formula formula,
        string text, bool theorem) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Module + decl), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(text))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula V(string name) => F.Id(name);
    private static Formula App(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(name))) :
            Seq(Operatorname, Grp(F.Id(name)), Parenthesized(Args(args)));
    private static Formula Args(Formula[] args) => args.Length == 0 ? Seq() :
        Seq(args.SelectMany((a, i) => i == 0 ? new[] { a } : new[] { Comma, Sp, a }).ToArray());
    private static Formula All(string name, Formula body) =>
        Seq(Forall, Sp, V(name), InMacro, Sp, N, Comma, Sp, body);
    private static Formula Parameters(Formula body) => All("b", All("p", All("q", body)));
    private static Formula At(string name, Formula n) => App(name, V("b"), V("p"), V("q"), n);
    private static Formula Succ(Formula n) => Seq(n, Plus, Sp, D(1));
    private static Formula Pow(Formula n) => new Formula.Power(V("b"), n);
    private static Formula Cast(Formula n) => Parenthesized(Seq(n, Colon, Sp, R));
    private static Formula Quotient => new Formula.Fraction(Cast(V("p")), Cast(V("q")));
    private static Formula Lambda(string n, Formula body) =>
        Parenthesized(Seq(App("fun"), Sp, V(n), Colon, Sp, N, Mapsto, Sp, body));
    private static Formula Assumptions => Seq(D(1), Lt, Sp, V("b"), Land, Sp, V("p"), Lt, Sp, V("q"));
    private static Formula RemainderFormula() => Disp(Parameters(Seq(
        At("remainder", D(0)), Eq, Sp, V("p"), Land, Sp,
        All("n", Seq(At("remainder", Succ(V("n"))), Eq, Sp,
            App("mod", Seq(V("b"), At("remainder", V("n"))), V("q")))))));
    private static Formula DigitFormula() => Disp(Parameters(All("n", Seq(
        At("digit", V("n")), Eq, Sp,
        new Formula.Fraction(Seq(V("b"), At("remainder", V("n"))), V("q"))))));
    private static Formula PrefixFormula() => Disp(Parameters(Seq(
        At("longDivisionPrefix", D(0)), Eq, Sp, D(0), Land, Sp,
        All("n", Seq(At("longDivisionPrefix", Succ(V("n"))), Eq, Sp,
            V("b"), At("longDivisionPrefix", V("n")), Plus, Sp, At("digit", V("n")))))));
    private static Formula InvariantFormula() => Disp(Parameters(All("n", Seq(
        V("q"), At("longDivisionPrefix", V("n")), Plus, Sp, At("remainder", V("n")),
        Eq, Sp, Pow(V("n")), V("p")))));
    private static Formula ValueFormula()
    {
        Formula term = new Formula.Fraction(Cast(At("digit", V("n"))),
            new Formula.Power(Cast(V("b")), Succ(V("n"))));
        Formula sequence = new Formula.Fraction(Cast(At("longDivisionPrefix", V("n"))),
            new Formula.Power(Cast(V("b")), V("n")));
        return Disp(Parameters(Seq(Assumptions, Rightarrow, Sp,
            App("HasSum", Lambda("n", term), Quotient), Land, Sp,
            App("Tendsto", Lambda("n", sequence), App("atTop"), App("nhds", Quotient)))));
    }
    private static Formula PeriodFormula()
    {
        Formula kernel = Parenthesized(Seq(Pow(V("L")), Minus, Sp, D(1)));
        Formula periodic = All("n", Seq(At("digit", Seq(V("n"), Plus, Sp, V("L"))),
            Eq, Sp, At("digit", V("n"))));
        Formula shift = Seq(Parenthesized(Seq(new Formula.Power(Cast(V("b")), V("L")),
            Minus, Sp, D(1))), Quotient, Eq, Sp, Cast(At("longDivisionPrefix", V("L"))));
        return Disp(Parameters(Seq(Assumptions, Rightarrow, Sp,
            All("L", Seq(V("q"), Mid, Sp, kernel, Rightarrow, Sp,
                Parenthesized(periodic), Land, Sp, shift)))));
    }
}
