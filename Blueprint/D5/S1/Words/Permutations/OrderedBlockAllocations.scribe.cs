using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Permutations;

internal sealed class OrderedBlockAllocationsDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S1/Words/Permutations/OrderedBlockAllocations.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered allocations factor permutations and determine the first-block minimum mean.",
        H("Ordered block allocations"),
        Blocks(
            Node("Allocation", "Allocations with prescribed fiber sizes", AllocationBody(),
                "An allocation assigns a label to every letter and has the same fiber cardinality "
                    + "at every label as c. The subtype retains the assignment and its cardinality equalities.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("IncreasingOnBlocks", "Increasing order in each block", IncreasingBody(),
                "Positions with equal c-labels have their letters in strictly increasing order.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("allocation_card_factorial", "The factorial factorization", FactorialBody(),
                "Every permutation determines its allocation by sorting the letters in each source fiber. "
                    + "The remaining choices are independent permutations internal to each fiber. "
                    + "This constructs a bijection and gives the cardinality factorization.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("weighted_increasing_blocks", "The mean minimum of the first block", WeightedBody(),
                "The first letter is the minimum of the letters allocated to the block containing position zero. "
                    + "For a positive d-element subset of {0,...,n-1}, summing its minimum plus one gives "
                    + "Nat.choose (n+1) (d+1). Equally sized fibers of allocations then give this weighted identity.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("card_increasingOnBlocks", "Sorting identifies the two cardinalities", CardinalityBody(),
                "Sorting each allocated fiber is inverse to extracting labels with the inverse permutation.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("ordered-block-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Root + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Naturals => Seq(Mathbb, Grp(V("N")));
    private static Formula Rationals => Seq(Mathbb, Grp(V("Q")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Q(params string[] names)
    {
        var items = new Formula[names.Length * 2 - 1];
        for (var i = 0; i < names.Length; i++)
        {
            items[i * 2] = V(names[i]);
            if (i + 1 < names.Length) items[i * 2 + 1] = Dot;
        }
        return Seq(Operatorname, Grp(items));
    }
    private static Formula App(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Subtype(string name, Formula type, Formula predicate) => Seq(
        OpenBrace, V(name), Colon, Sp, type, Sp, Vert, Sp, predicate, CloseBrace);
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula Cast(Formula x) => Parenthesized(Seq(App(Q("Nat", "cast"), x), Colon, Sp, Rationals));
    private static Formula Card(Formula type) => App(Q("Fintype", "card"), type);
    private static Formula Instance(string name, Formula type) => Seq(OpenBracket, Call(name, type), CloseBracket, Sp);
    private static Formula Fiber(Formula c, Formula j, Formula alpha) => Subtype("a", alpha,
        Equal(App(c, V("a")), j));
    private static Formula Parameters(Formula body, bool finiteAlpha = true, bool orderedAlpha = true,
        bool finiteLabels = true, bool decidableLabels = true) =>
        All("alpha", V("Type"), All("iota", V("Type"), Seq(
            finiteAlpha ? Instance("Fintype", V("alpha")) : Seq(),
            orderedAlpha ? Instance("LinearOrder", V("alpha")) : Seq(),
            finiteLabels ? Instance("Fintype", V("iota")) : Seq(),
            decidableLabels ? Instance("DecidableEq", V("iota")) : Seq(),
            All("c", Arrow(V("alpha"), V("iota")), body))));
    private static Formula Permutations(Formula alpha) => App(Q("Equiv", "Perm"), alpha);
    private static Formula OrderedPermutations(Formula alpha) => Subtype("pi", Permutations(alpha),
        Call("IncreasingOnBlocks", V("c"), V("pi")));
    private static Formula AllocationBody()
    {
        var fibers = All("j", V("iota"), Equal(Card(Fiber(V("f"), V("j"), V("alpha"))),
            Card(Fiber(V("c"), V("j"), V("alpha")))));
        return Parameters(Equal(Call("Allocation", V("c")),
            Subtype("f", Arrow(V("alpha"), V("iota")), fibers)),
            orderedAlpha: false, finiteLabels: false);
    }
    private static Formula IncreasingBody()
    {
        var body = All("a", V("alpha"), All("b", V("alpha"), Seq(
            Equal(App(V("c"), V("a")), App(V("c"), V("b"))), Sp, Implies, Sp,
            V("a"), Sp, Lt, Sp, V("b"), Sp, Implies, Sp,
            App(V("pi"), V("a")), Sp, Lt, Sp, App(V("pi"), V("b")))));
        return Parameters(All("pi", Permutations(V("alpha")),
            Equal(Call("IncreasingOnBlocks", V("c"), V("pi")), Parenthesized(body))),
            finiteAlpha: false, finiteLabels: false, decidableLabels: false);
    }
    private static Formula FactorialBody() => Parameters(Equal(
        Seq(Card(Call("Allocation", V("c"))), Sp, Cdot, Sp,
            Parenthesized(Seq(new Formula.Subscript(Prod, Seq(V("j"), Colon, Sp, V("iota"))), Sp,
                App(Q("Nat", "factorial"), Card(Fiber(V("c"), V("j"), V("alpha"))))))),
        App(Q("Nat", "factorial"), Card(V("alpha")))));
    private static Formula CardinalityBody() => Parameters(Equal(Card(OrderedPermutations(V("alpha"))),
        Card(Call("Allocation", V("c")))));
    private static Formula WeightedBody()
    {
        var alpha = Call("Fin", V("n"));
        var zero = App(Q("Fin", "mk"), D(0), V("hn"));
        var letter = Seq(Q("if"), Sp, V("h"), Colon, Sp, D(0), Sp, Lt, Sp, V("n"), Sp,
            Q("then"), Sp, Add(Val(App(Val(V("p")), App(Q("Fin", "mk"), D(0), V("h")))), D(1)),
            Sp, Q("else"), Sp, D(0));
        var sum = Seq(new Formula.Subscript(Sum,
            Seq(V("p"), Colon, Sp, OrderedPermutations(alpha))), Sp, Cast(Parenthesized(letter)));
        var body = Equal(Seq(Cast(Add(Card(Fiber(V("c"), App(V("c"), zero), alpha)), D(1))),
                Sp, Cdot, Sp, Parenthesized(sum)),
            Seq(Parenthesized(Add(Cast(V("n")), D(1))), Sp, Cdot, Sp, Cast(Card(OrderedPermutations(alpha)))));
        return All("n", Naturals, All("hn", Seq(D(0), Sp, Lt, Sp, V("n")),
            All("iota", V("Type"), Seq(Instance("Fintype", V("iota")), Instance("DecidableEq", V("iota")),
                All("c", Arrow(alpha, V("iota")), body)))));
    }
}
