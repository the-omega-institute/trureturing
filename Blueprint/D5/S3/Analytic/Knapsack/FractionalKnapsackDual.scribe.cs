using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Knapsack;

internal sealed class FractionalKnapsackDualDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A decreasing return-to-weight ratio orders a greedy maximizer, and a threshold price attains the dual minimum.",
        H("Fractional knapsack and its dual price"),
        Blocks(
            Paragraph(Text(
                "Let I be an arbitrary finite index type with decidable equality, and let w and v be real functions on I. Write C for cost, V for return, D for the scalar dual value, and F for the feasible set at a real budget B. For the first two theorems, assume that all weights are strictly positive, all returns are nonnegative, and B is nonnegative.")),
            Paragraph(Math(Disp(DefinitionsFormula()))),
            Paragraph(Math(Disp(FeasibleFormula()))),
            Describe.Lean(
                DescribeId.Create("fractional-knapsack-strong-duality"),
                DeclarationHandle.Create("D5/S3/Analytic/Knapsack/FractionalKnapsackDual.fractional_knapsack_strong_duality"),
                H("Equality of primal and dual values"),
                StatementSource.FromAuthor(Disp(Seq(Primal(), Sp, Eq, Sp, Dual()))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume every weight is strictly positive, every return is nonnegative, and B is nonnegative. Then the supremum of the return over F equals the infimum of D over nonnegative real prices. This equality refers only to the original weights, returns and budget; no ordering of I is a hypothesis. The infimum ranges over the type of nonnegative real prices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("greedy-attains-duality"),
                DeclarationHandle.Create("D5/S3/Analytic/Knapsack/FractionalKnapsackDual.greedy_attains_duality"),
                H("A greedy allocation and a minimizing price"),
                StatementSource.FromAuthor(Disp(GreedyFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the same positive-weight, nonnegative-return and nonnegative-budget assumptions, there is a list l containing each index exactly once and a nonnegative price p. Sorted(l) means that whenever i precedes j in l, v(j)/w(j) is at most v(i)/w(i). The notation g with subscript l denotes greedyFill(w,l,B).")),
                    Paragraph(Text(
                        "The greedy rule starts with remaining budget B. An empty list gives the zero allocation. If the first weight does not exceed the remaining budget, that item receives one and the rule continues on the tail with that weight subtracted. Otherwise the first item receives the fraction theta equal to the remaining budget divided by its weight, and every later item receives zero. Positivity of the weight and the stopping inequality give zero less than or equal to theta and theta strictly less than one.")),
                    Paragraph(Text(
                        "Induction by the largest ratio constructs both the list and the price. When the budget stops within the first item, use that item's ratio as the price. Every remaining item's reduced return is nonpositive. When the first item is filled, use the price constructed for the tail. That price is either zero or the ratio of a tail item, so it is at most the first ratio. These two cases give the coordinate identities and the budget identity displayed above.")),
                    Paragraph(Text(
                        "For every feasible allocation t and nonnegative price p, the coordinate bounds give (v(i)-p w(i))t(i) at most max(0,v(i)-p w(i)). Summing and applying the budget inequality gives V(t) at most D(p). The constructed allocation attains equality because the coordinate identities sum exactly and p times the unused budget is zero. Thus the primal supremum is a maximum and the dual infimum is a minimum. Empty index sets and zero budgets are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("full-budget-optimum"),
                DeclarationHandle.Create("D5/S3/Analytic/Knapsack/FractionalKnapsackDual.full_budget_optimum"),
                H("Enough budget to fill every item"),
                StatementSource.FromAuthor(Disp(FullBudgetFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For this assertion the weights and budget may be arbitrary real numbers: it suffices that every return is nonnegative and the sum of the weights is at most B. Writing e for the constant-one allocation, e belongs to F, both optimal values are the sum of all returns, and price zero attains that value. Indeed the constant-one allocation is feasible and D(0) equals its return. The general upper bound then settles both extrema."))),
                DescribeRole.Theorem))));

    private static Formula SumOverI(Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("I")), Sp, body);

    private static Formula Primal() => Seq(
        Operatorname, Grp(F.Id("sup")), Underscore,
        Grp(F.Id("t"), Sp, InMacro, Sp, F.Id("F")), Sp, Call("V", F.Id("t")));

    private static Formula Dual() => Seq(
        Operatorname, Grp(F.Id("inf")), Underscore,
        Grp(F.Id("p"), Sp, Ge, Sp, D(0)), Sp, Call("D", F.Id("p")));

    private static Formula ReducedReturn() => Seq(
        Call("v", F.Id("i")), Minus, F.Id("p"), Call("w", F.Id("i")));

    private static Formula PositivePart() => Seq(
        Max, Open, D(0), Comma, ReducedReturn(), Close);

    private static Formula DefinitionsFormula() => Seq(
        Call("C", F.Id("t")), Sp, Eq, Sp,
        SumOverI(Seq(Call("w", F.Id("i")), Call("t", F.Id("i")))), Comma, Sp,
        Call("V", F.Id("t")), Sp, Eq, Sp,
        SumOverI(Seq(Call("v", F.Id("i")), Call("t", F.Id("i")))), Comma, Sp,
        Call("D", F.Id("p")), Sp, Eq, Sp, F.Id("p"), F.Id("B"), Plus,
        SumOverI(PositivePart()));

    private static Formula FeasibleFormula() => Seq(
        F.Id("F"), Sp, Eq, Sp, OpenBrace,
        F.Id("t"), Colon, F.Id("I"), Sp, To, Sp, Mathbb, Grp(F.Id("R")), Sp, Mid, Sp,
        Open, Forall, Sp, F.Id("i"), Sp, InMacro, Sp, F.Id("I"), Comma, Sp,
        D(0), Sp, Le, Sp, Call("t", F.Id("i")), Sp, Le, Sp, D(1), Close,
        Sp, Land, Sp, Call("C", F.Id("t")), Sp, Le, Sp, F.Id("B"), CloseBrace);

    private static Formula GreedyFormula()
    {
        Formula l = F.Id("l");
        Formula p = F.Id("p");
        Formula g = Seq(F.Id("g"), Underscore, Grp(l));
        return Seq(
            Exists, Sp, l, Colon, Call("List", F.Id("I")), Comma, Sp,
            Exists, Sp, p, Colon, Mathbb, Grp(F.Id("R")), Comma, Sp,
            Call("Nodup", l), Sp, Land, Sp, Call("set", l), Sp, Eq, Sp, F.Id("I"),
            Sp, Land, Sp, Call("Sorted", l), Sp, Land, Sp, g, Sp, InMacro, Sp, F.Id("F"),
            Sp, Land, Sp, D(0), Sp, Le, Sp, p,
            Sp, Land, Sp, p, Open, F.Id("B"), Minus, Call("C", g), Close, Sp, Eq, Sp, D(0),
            Sp, Land, Sp, Open, Forall, Sp, F.Id("i"), Sp, InMacro, Sp, F.Id("I"), Comma, Sp,
            Open, ReducedReturn(), Close, g, Open, F.Id("i"), Close, Sp, Eq, Sp,
            PositivePart(), Close,
            Sp, Land, Sp, Call("V", g), Sp, Eq, Sp, Call("D", p),
            Sp, Land, Sp, Primal(), Sp, Eq, Sp, Call("V", g),
            Sp, Land, Sp, Dual(), Sp, Eq, Sp, Call("V", g));
    }

    private static Formula FullBudgetFormula() => Seq(
        F.Id("e"), Sp, InMacro, Sp, F.Id("F"), Sp, Land, Sp,
        Primal(), Sp, Eq, Sp, SumOverI(Call("v", F.Id("i"))), Sp, Land, Sp,
        Dual(), Sp, Eq, Sp, SumOverI(Call("v", F.Id("i"))), Sp, Land, Sp,
        Call("D", D(0)), Sp, Eq, Sp, SumOverI(Call("v", F.Id("i"))));
}
