using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Derangements;

internal sealed class TerminalDifferenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Derangements/TerminalDifference.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/kagey2024a378495");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every natural n at least five, the difference T(n,n-2)-T(n,n) for derangements avoiding a cycle length is (n-3)!(n-4)(n-1)/2.",
        H("The Terminal Difference of the Derangement Triangle"),
        Blocks(
            Node("derangement-set", "Derangements on n labels", "D",
                "For every natural n, D(n) is the finite set of all permutations p of Fin n such that p(x) differs from x for every label x. The labels are the integers from zero to n-1. Relabelling them from one to n gives the symmetric group in the source definition. At n=0 the empty permutation satisfies the condition vacuously; no positivity assumption is built into D.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("triangle-count", "The triangle entry", "T",
                "For natural n and k, T(n,k) is the cardinality of the subset of D(n) in which every cycle factor has support cardinality different from k. On the source range 1 <= k <= n this counts exactly the derangements with no k-cycle. Cycle factors omit fixed points, which D already excludes, so forbidding a 1-cycle imposes no additional restriction. The definition is total also at zero and outside the triangular range; the identity below uses only source-range columns.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("excluded-set", "Derangements containing a forbidden cycle", "excluded",
                "For natural n and k, excluded(n,k) is the subset of D(n) whose multiset of nontrivial cycle lengths contains k. Membership records the existence of at least one such cycle, rather than counting occurrences or selecting a distinguished cycle. Its cardinality therefore counts excluded permutations once each.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("cycle-membership", "Cycle factors and cycle type", "noCycle_iff",
                "For every natural n and k and every permutation p of Fin n, all cycle factors of p have support cardinality different from k if and only if k is absent from p's cycle type. The cycle type is the multiset of support sizes of the nontrivial cycle factors. No derangement or positivity assumption is needed for this equivalence, including k=0 and k=1.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("partition-count", "The excluded and retained permutations partition D", "T_add_excluded",
                "For every natural n and k, T(n,k) plus the cardinality of excluded(n,k) equals the cardinality of D(n). The two filters are complementary predicates on the same finite set; a permutation with several k-cycles still belongs to only one part. This is an equality of natural cardinalities and involves no subtraction.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("fixed-point-sum", "Recognizing derangements from cycle type", "noFixed_iff_sum",
                "For every natural n and permutation p of Fin n, p has no fixed point if and only if the sum of its nontrivial cycle lengths is n. That sum is the cardinality of the support of p; on an n-label set it equals n precisely when every label is moved. The equivalence includes the empty permutation at n=0.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("sum-two", "A multiset of total size two", "sum_two",
                "For any multiset s of natural numbers, if its sum is two and every member is at least two, then s is the singleton multiset containing two. A nonempty remainder would contribute at least two more to the sum. The lower bound on every member rules out zero entries and entries of size one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("terminal-type", "The terminal cycle type", "terminal_cycleType",
                "For every natural n and permutation p of Fin n, being a derangement and having n in the cycle type is equivalent to having cycle type exactly the singleton multiset containing n. An n-cycle exhausts the labels. There is no lower-bound hypothesis: when n is zero or one, both sides are false because cycle type contains only lengths at least two.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("penultimate-type", "The cycle type containing n-2", "penultimate_cycleType",
                "For every natural n at least five and permutation p of Fin n, being a derangement with n-2 in its cycle type is equivalent to having cycle type exactly the two-member multiset containing n-2 and two. Removing the n-2 part leaves total size two, and all remaining parts are at least two. The bound makes n-2 at least three, so these two lengths are distinct. All index subtractions are natural subtraction.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("terminal-card", "Counting the excluded n-cycles", "excluded_terminal_card",
                "For every natural n at least five, the cardinality of excluded(n,n) is (n-1)!. These are exactly the permutations with cycle type consisting of n alone. The singleton cycle-type counting formula gives (n-1)! times choose(n,n), and the binomial factor is one. Factorial and n-1 are natural-number operations.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("penultimate-card", "Counting the excluded two-cycle types", "excluded_penultimate_mul",
                "For every natural n at least five, the cardinality of excluded(n,n-2), multiplied by 2(n-2), is n!. The contributing cycle type consists of two distinct lengths n-2 and two, covers all labels and has multiplicity one for each length. Its cycle-count denominator is therefore 2(n-2). This is a division-free equality in the natural numbers; n-2 is positive under the stated bound.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("terminal-result", "The terminal-column identity", "result",
                "For every natural n with 5 <= n, cast both triangle cardinalities to the rationals before subtracting. In the formulas, castQ denotes the natural-number embedding into the rationals. Their difference T(n,n-2)-T(n,n) equals (n-3)!(n-4)(n-1)/2, with the factorial and all index subtractions evaluated in the natural numbers and then cast to the rationals. The only hypothesis is 5 <= n, with no upper bound. The partition identity turns the difference into (n-1)! minus the number of permutations of cycle type (n-2,2). Substituting their count n!/(2(n-2)) and expanding factorials yields the displayed expression. Cancellation is valid because n-2 is nonzero; the bound also justifies replacing casts of n-4 and n-1 by rational subtraction. The final division by two is rational division.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("a378495-terminal-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Statement(declaration))),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Statement(string declaration)
    {
        Formula n = F.Id("n"), k = F.Id("k"), p = F.Id("p"), s = F.Id("s");
        var types = Call("cycleType", p);
        var noFixed = All("x", Call("Fin", n), Ne(Apply(p, F.Id("x")), F.Id("x")));
        var noCycle = All("c", Call("cycleFactorsFinset", p),
            Ne(Card(Call("support", F.Id("c"))), k));
        var deranged = Mem(p, Call("derangements", Call("Fin", n)));
        var terminal = Iff(And(deranged, Mem(n, types)), Eqn(types, Call("multiset", n)));
        var penultimate = Iff(And(deranged, Mem(Subtract(n, D(2)), types)),
            Eqn(types, Call("multiset", Subtract(n, D(2)), D(2))));
        var bound = Le(D(5), n);
        var d = Call("D", n);
        return declaration switch
        {
            "D" => All("n", Nat(), Eqn(d,
                SetOf(p, Call("Perm", Call("Fin", n)), noFixed))),
            "T" => All("n", Nat(), All("k", Nat(),
                Eqn(Call("T", n, k), Card(SetOf(p, d, noCycle))))),
            "excluded" => All("n", Nat(), All("k", Nat(),
                Eqn(Call("excluded", n, k), SetOf(p, d, Mem(k, types))))),
            "noCycle_iff" => All("n", Nat(), All("k", Nat(),
                All("p", Call("Perm", Call("Fin", n)),
                    Iff(noCycle, new Formula.Not(Mem(k, types)))))),
            "T_add_excluded" => All("n", Nat(), All("k", Nat(),
                Eqn(Add(Call("T", n, k), Card(Call("excluded", n, k))), Card(d)))),
            "noFixed_iff_sum" => All("n", Nat(),
                All("p", Call("Perm", Call("Fin", n)),
                    Iff(deranged, Eqn(Call("sum", types), n)))),
            "sum_two" => All("s", Call("Multiset", Nat()),
                Implies(Eqn(Call("sum", s), D(2)),
                    Implies(All("a", s, Le(D(2), F.Id("a"))),
                        Eqn(s, Call("multiset", D(2)))))),
            "terminal_cycleType" => All("n", Nat(),
                All("p", Call("Perm", Call("Fin", n)), terminal)),
            "penultimate_cycleType" => All("n", Nat(), Implies(bound,
                All("p", Call("Perm", Call("Fin", n)), penultimate))),
            "excluded_terminal_card" => All("n", Nat(), Implies(bound,
                Eqn(Card(Call("excluded", n, n)), Factorial(Subtract(n, D(1)))))),
            "excluded_penultimate_mul" => All("n", Nat(), Implies(bound,
                Eqn(Multiply(Card(Call("excluded", n, Subtract(n, D(2)))),
                    Multiply(D(2), Subtract(n, D(2)))), Factorial(n)))),
            "result" => All("n", Nat(), Implies(bound,
                Eqn(Subtract(CastQ(Call("T", n, Subtract(n, D(2)))),
                        CastQ(Call("T", n, n))),
                    new Formula.Fraction(
                        Multiply(Multiply(CastQ(Factorial(Subtract(n, D(3)))),
                            CastQ(Subtract(n, D(4)))), CastQ(Subtract(n, D(1)))), D(2))))),
            _ => throw new System.ArgumentException("Unknown declaration", nameof(declaration))
        };
    }

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);
    private static Formula Card(Formula value) => Call("card", value);
    private static Formula CastQ(Formula value) => Call("castQ", value);
    private static Formula Factorial(Formula value) => Seq(Open, value, Close, Bang);
    private static Formula SetOf(Formula variable, Formula domain, Formula predicate) =>
        Seq(OpenBrace, variable, Sp, InMacro, Sp, domain, Sp, Mid, Sp, predicate, CloseBrace);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Mem(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
