using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ErdosUlam;

internal sealed class UnionClosedCountRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent choices on a level of the Boolean lattice give too many labelled "
            + "union-closed families for the proposed quasipolynomial threshold.",
        H("Union-closed counting exceeds the proposed threshold"),
        Blocks(
            Paragraph(Text("Bhattacharjee, Mandal and Bhattacharya ask in Question 9.2 of "
                + "arXiv:2610.02833v1 whether a constant C makes the number of union-closed "
                + "families of size N less than two to the power N minus one whenever N is "
                + "at least n to the power C times the iterated base-two logarithm of n, "
                + "for all sufficiently large n. Families are labelled subsets of the Boolean lattice.")),
            Node("count", "The labelled count", "U", CountFormula(),
                "Count finite families with exactly N members and closed under every binary union. "
                    + "No equivalence under permutations of the ground set is imposed.", DescribeRole.Definition),
            Node("threshold-claim", "The asserted eventual bound", "claim", ClaimFormula(),
                "The real constant and the natural cutoff precede the universal quantifiers over "
                    + "dimension and family size. Natural subtraction occurs only in the integer "
                    + "exponent N minus one.", DescribeRole.Definition),
            Node("tail", "A strict quarter-tail bound", "binomial_tail_bound", TailFormula(),
                "Write B for the r-th binomial coefficient in dimension six r and H for the "
                    + "sum of coefficients below it. The successive-coefficient identity gives "
                    + "(five r plus one) times each coefficient at most r times the next. Summing "
                    + "gives (four r plus one) H at most r times (B minus one), hence four H is less than B.",
                DescribeRole.Theorem),
            Node("growth", "Exponential growth of the chosen level", "binomial_level_growth", GrowthFormula(),
                "Vandermonde's identity gives at least six choices for each additional block of "
                    + "six points. Induction yields B at least six to the power r.", DescribeRole.Theorem),
            Node("injection", "Independent four-way selections", "level_selection_injection", InjectionFormula(),
                "Embed q disjoint quadruples in the level of k-element subsets. For each function "
                    + "from q indices to four choices, include its q selected sets and every set "
                    + "of cardinality greater than k. This family is upward-closed: any strict "
                    + "superset of a selected set belongs to the upper tail. Its size is the "
                    + "upper-tail size plus q, and distinct functions give distinct families.", DescribeRole.Theorem),
            Node("count-lower", "The resulting counting lower bound", "level_selection_count", SelectionCountFormula(),
                "The injection supplies at least four to the power q distinct union-closed "
                    + "families at the specified size.", DescribeRole.Theorem),
            Node("complement", "Complementation identifies the tails", "upper_tail_card", UpperTailFormula(),
                "Complementation bijects subsets of size greater than five r with subsets of "
                    + "size less than r. Partitioning the latter by cardinality gives H.", DescribeRole.Theorem),
            Node("counterexamples", "Exponential-sized counterexamples", "counting_counterexample", CounterexampleFormula(),
                "Set q to the integer quotient B divided by four and N to H plus q. The tail "
                    + "bound gives H at most q. Thus two to the power N is at most four to the "
                    + "power q and hence at most the labelled count. For r at least four, the "
                    + "level-growth estimate also gives N at least two to the power r.", DescribeRole.Theorem),
            Node("threshold", "The threshold is eventually met", "eventual_threshold", ThresholdFormula(),
                "For any real C, the square of the base-two logarithm divided by dimension "
                    + "tends to zero. The iterated logarithm is bounded by the first logarithm "
                    + "divided by log two. Consequently the exponent after conversion to base "
                    + "two is eventually at most r, even for an arbitrary fixed C.", DescribeRole.Theorem),
            Node("refutation", "Question 9.2 has a negative answer", "result", Disp(new Formula.Not(F.Id("claim"))),
                "Choose r large enough to exceed the dimension cutoff and meet the threshold. "
                    + "The constructed size N satisfies the hypothesis while its count is at least "
                    + "two to the power N, contradicting the asserted strict upper bound. This "
                    + "settles the counting question; it does not refute the underlying "
                    + "Erdős–Ulam union-closed extremal problem or Proposition 5.4's conditional implication.",
                DescribeRole.Theorem, new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bhattacharjee-mandal-bhattacharya-2026-union-closed-count-refutation"),
                    ResolutionKind.Refuted))), []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Real() => new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
    private static Formula Sets(Formula n) => Call("Finset", Call("Fin", n));
    private static Formula Families(Formula n) => Call("Finset", Sets(n));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Six(Formula r) => Mul(D(6), r);
    private static Formula Choose(Formula n, Formula k) => Call("choose", n, k);
    private static Formula Card(Formula a) => Call("card", a);
    private static Formula Collection(string variable, Formula type, Formula predicate) =>
        Seq(OpenBrace, Sp, F.Id(variable), Sp, Colon, Sp, type, Sp, Bar, Sp, predicate, Sp, CloseBrace);
    private static Formula Upper(Formula n, Formula k) =>
        Card(Collection("A", Sets(n), Lt(k, Card(F.Id("A")))));
    private static Formula Tail(Formula r) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id("i"), Sp, InMacro, Sp, Call("range", r))), Sp, Choose(Six(r), F.Id("i")));
    private static Formula Size(Formula r) =>
        Add(Tail(r), Call("NatDiv", Choose(Six(r), r), D(4)));
    private static Formula Threshold(Formula n, Formula c) =>
        Pow(Call("castReal", n), Mul(c, Call("logb", D(2), Call("logb", D(2), Call("castReal", n)))));
    private static Formula Closed(Formula n, Formula f) => All("A", Sets(n), Imp(Mem(F.Id("A"), f),
        All("B", Sets(n), Imp(Mem(F.Id("B"), f), Mem(Call("union", F.Id("A"), F.Id("B")), f)))));
    private static Formula CountFormula()
    {
        var n = F.Id("n"); var m = F.Id("N"); var f = F.Id("F");
        return Disp(All("n", Nat(), All("N", Nat(), Eqn(Call("U", n, m),
            Card(Collection("F", Families(n), And(Eqn(Card(f), m), Closed(n, f))))))));
    }
    private static Formula ClaimFormula()
    {
        var c = F.Id("C"); var z = F.Id("cutoff"); var n = F.Id("n"); var m = F.Id("N");
        return Disp(Iff(F.Id("claim"), Ex("C", Real(), Ex("cutoff", Nat(), All("n", Nat(),
            Imp(Le(z, n), All("N", Nat(), Imp(Le(Threshold(n, c), Call("castReal", m)),
                Lt(Call("U", n, m), Pow(D(2), Sub(m, D(1))))))))))));
    }
    private static Formula TailFormula()
    {
        var r = F.Id("r");
        return Disp(All("r", Nat(), Imp(Le(D(1), r), Lt(Mul(D(4), Tail(r)), Choose(Six(r), r)))));
    }
    private static Formula GrowthFormula()
    {
        var r = F.Id("r");
        return Disp(All("r", Nat(), Le(Pow(D(6), r), Choose(Six(r), r))));
    }
    private static Formula InjectionFormula()
    {
        var n = F.Id("n"); var k = F.Id("k"); var q = F.Id("q"); var f = F.Id("f"); var x = F.Id("x");
        var choices = new Formula.TypeArrow(Call("Fin", q), Call("Fin", D(4)));
        return Disp(All("n", Nat(), All("k", Nat(), All("q", Nat(), Imp(Le(Mul(D(4), q), Choose(n, k)),
            Ex("f", new Formula.TypeArrow(choices, Families(n)), And(Call("Injective", f),
                All("x", choices, And(Eqn(Card(Call("f", x)), Add(Upper(n, k), q)), Closed(n, Call("f", x)))))))))));
    }
    private static Formula SelectionCountFormula()
    {
        var n = F.Id("n"); var k = F.Id("k"); var q = F.Id("q");
        return Disp(All("n", Nat(), All("k", Nat(), All("q", Nat(), Imp(Le(Mul(D(4), q), Choose(n, k)),
            Le(Pow(D(4), q), Call("U", n, Add(Upper(n, k), q))))))));
    }
    private static Formula UpperTailFormula()
    {
        var r = F.Id("r");
        return Disp(All("r", Nat(), Eqn(Upper(Six(r), Mul(D(5), r)), Tail(r))));
    }
    private static Formula CounterexampleFormula()
    {
        var r = F.Id("r");
        return Disp(All("r", Nat(), Imp(Le(D(4), r), And(Le(Pow(D(2), r), Size(r)),
            Le(Pow(D(2), Size(r)), Call("U", Six(r), Size(r)))))));
    }
    private static Formula ThresholdFormula()
    {
        var c = F.Id("C"); var z = F.Id("cutoff"); var r = F.Id("r");
        return Disp(All("C", Real(), Ex("cutoff", Nat(), All("r", Nat(), Imp(Le(z, r),
            Le(Threshold(Six(r), c), Pow(D(2), r)))))));
    }
}
