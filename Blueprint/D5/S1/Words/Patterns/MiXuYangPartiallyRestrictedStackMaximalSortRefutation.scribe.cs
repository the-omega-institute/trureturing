using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns;

internal sealed class MiXuYangPartiallyRestrictedStackMaximalSortRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/mixuyang2025partialstacks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mi, Xu and Yang's Conjecture 5.2 is false at n=3 for the permutation 132.",
        H("A Counterexample to the Maximal-Sort Characterization"),
        Blocks(
            Paragraph(Text(
                "The stack is listed from top to bottom. The paper's map s_(T,k) reads input "
                    + "from left to right, pushes when the proposed stack remains (T,k)-avoiding, "
                    + "and otherwise emits the top and retries the same input. The remaining stack "
                    + "is emitted top-first. West's s is the instance with T={21}, k=0, while t is "
                    + "the instance with T={12,21}, k=1.")),
            Node("contains", "Pattern containment", "Contains", ContainsFormula(),
                "A finite Boolean scan of the subsequences backs this Prop definition. Equal length "
                    + "and agreement of every strict-order comparison express order-isomorphism. "
                    + "This is the containment definition on printed page 2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("tk-avoiding", "Partially restricted avoidance", "TkAvoiding",
                TkAvoidingFormula(),
                "T is read as the set of its distinct members, following the paper's phrase "
                    + "'k distinct permutations from T' on printed page 1. The displayed "
                    + "cardinality is the number of distinct members of T contained in w, and it "
                    + "is at most k. This is the (T,k)-avoiding definition on printed page 2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("stack-run", "The partially restricted stack map", "stackRun",
                StackRunFormula(),
                "The private data function pushInput either pushes x and emits nothing, or emits "
                    + "the current top and recursively retries x against the remaining stack. "
                    + "stackRun drains the top-first stack when the input is empty. These equations "
                    + "implement the push, pop-and-retry, and flush rules on printed page 1. The "
                    + "mirror's s_(T,k) is the page-1 machine for pattern families whose members "
                    + "have length at least two, which covers s and t. With a length-one pattern, "
                    + "the paper leaves the empty-stack pop case undefined.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("west-s", "West's stack map", "s", SFormula(),
                "The singleton restriction list [21] with allowance zero makes the top-first stack "
                    + "avoid 21, exactly the paper's description of West's s on printed page 1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("partially-restricted-t", "The map t", "t", TFormula(),
                "The restriction list is [12,21] and the allowance is one, matching the notation "
                    + "t=s_({12,21},1) introduced on printed page 2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("takes-sorts", "Exact sorting time", "TakesSorts", TakesSortsFormula(),
                "iterate(f,j,pi) denotes the j-th iterate of f at pi. The first clause reaches the "
                    + "identity word of the same length, and the second clause excludes every "
                    + "earlier iterate. The rendered range' notation denotes Lean's List.range'. "
                    + "Thus j is the smallest nonnegative sorting time from "
                    + "printed page 6.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("lemma-form", "The proposed extremal form", "LemmaForm", LemmaFormFormula(),
                "The middle word sigma permutes the entries 3 through n-1 and avoids the pattern "
                    + "213. The full word begins with 2 and ends with 1,n, as in printed page 7.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conjecture", "Mi-Xu-Yang Conjecture 5.2", "claim", ClaimFormula(),
                "For every n at least 3 and every permutation pi of the one-based identity word, "
                    + "the asserted equivalence identifies sorting time 2n-5 with the proposed "
                    + "2 sigma 1 n form. Natural subtraction is truncated at zero; the lower bound "
                    + "makes both displayed differences ordinary nonnegative differences.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("refutation", "The conjecture is false", "result", ResultFormula(),
                "At n=3, t sends 132 to 321 and s sends 321 to 123. Thus 132 takes exactly one "
                    + "sort, which equals 2*3-5, but it cannot begin with 2 and so cannot have the "
                    + "form 2 sigma 1 3. This refutes the only-if direction.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("mi-xu-yang-" + id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role);

    private static Formula ContainsFormula()
    {
        var pi = Id("pi");
        var sigma = Id("sigma");
        var u = Id("u");
        var i = Id("i");
        var j = Id("j");
        var bounded = And(Less(i, Length(u)), Less(j, Length(u)));
        var orderAgreement = Iff(
            Less(new Formula.Apply(Seq(Id("getElem"), Bang), [u, i]),
                new Formula.Apply(Seq(Id("getElem"), Bang), [u, j])),
            Less(new Formula.Apply(Seq(Id("getElem"), Bang), [sigma, i]),
                new Formula.Apply(Seq(Id("getElem"), Bang), [sigma, j])));
        var witness = Some([Bound("u", Word())],
            And(Member(u, Call("sublists", pi)),
                And(Equal(Length(u), Length(sigma)),
                    All([Bound("i", Naturals()), Bound("j", Naturals())],
                        Implies(bounded, orderAgreement)))));
        return Disp(All([Bound("pi", Word()), Bound("sigma", Word())],
            Iff(Call("Contains", pi, sigma), Parenthesized(witness))));
    }

    private static Formula TkAvoidingFormula()
    {
        var patterns = Id("T");
        var k = Id("k");
        var w = Id("w");
        var sigma = Id("sigma");
        var contained = Seq(
            OpenBrace, sigma, Sp, InMacro, Sp, patterns, Sp, Mid, Sp,
            Call("Contains", w, sigma), CloseBrace);
        return Disp(All([
                Bound("T", PatternList()), Bound("k", Naturals()), Bound("w", Word())],
            Iff(Call("TkAvoiding", patterns, k, w),
                AtMost(Seq(Lvert, contained, Rvert), k))));
    }

    private static Formula StackRunFormula()
    {
        var patterns = Id("T");
        var k = Id("k");
        var x = Id("x");
        var a = Id("a");
        var rest = Id("rest");
        var stack = Id("stack");
        var xs = Id("xs");
        var proposed = Cons(x, Cons(a, rest));
        var recursivePush = Call("pushInput", patterns, k, x, rest);
        var pushed = Pair(EmptyList(), proposed);
        var popped = Pair(Cons(a, Call("fst", recursivePush)),
            Call("snd", recursivePush));
        var currentPush = Call("pushInput", patterns, k, x, stack);
        return Disp(new Formula.Aligned([
            All([Bound("T", PatternList()), Bound("k", Naturals()), Bound("x", Naturals())],
                Equal(Call("pushInput", patterns, k, x, EmptyList()),
                    Pair(EmptyList(), ListLiteral(x)))),
            All([
                    Bound("T", PatternList()), Bound("k", Naturals()),
                    Bound("x", Naturals()), Bound("a", Naturals()), Bound("rest", Word())],
                Equal(Call("pushInput", patterns, k, x, Cons(a, rest)),
                    Call("if", Call("TkAvoiding", patterns, k, proposed), pushed, popped))),
            All([Bound("T", PatternList()), Bound("k", Naturals()), Bound("stack", Word())],
                Equal(Call("stackRun", patterns, k, stack, EmptyList()), stack)),
            All([
                    Bound("T", PatternList()), Bound("k", Naturals()),
                    Bound("stack", Word()), Bound("x", Naturals()), Bound("xs", Word())],
                Equal(Call("stackRun", patterns, k, stack, Cons(x, xs)),
                    Call("append", Call("fst", currentPush),
                        Call("stackRun", patterns, k, Call("snd", currentPush), xs))))
        ]));
    }

    private static Formula SFormula()
    {
        var pi = Id("pi");
        return Disp(All([Bound("pi", Word())],
            Equal(Call("s", pi),
                Call("stackRun", ListLiteral(ListLiteral(D(2), D(1))), D(0), EmptyList(), pi))));
    }

    private static Formula TFormula()
    {
        var pi = Id("pi");
        return Disp(All([Bound("pi", Word())],
            Equal(Call("t", pi),
                Call("stackRun",
                    ListLiteral(ListLiteral(D(1), D(2)), ListLiteral(D(2), D(1))),
                    D(1), EmptyList(), pi))));
    }

    private static Formula TakesSortsFormula()
    {
        var pi = Id("pi");
        var j = Id("j");
        var i = Id("i");
        var identity = RangePrime(D(1), Length(pi));
        var atJ = Equal(Iterate(j, pi), identity);
        var earlier = All([Bound("i", Naturals())],
            Implies(Less(i, j), NotEqual(Iterate(i, pi), identity)));
        return Disp(All([Bound("pi", Word()), Bound("j", Naturals())],
            Iff(Call("TakesSorts", pi, j), And(atJ, earlier))));
    }

    private static Formula LemmaFormFormula()
    {
        var n = Id("n");
        var pi = Id("pi");
        var sigma = Id("sigma");
        var word = Cons(D(2), Call("append", sigma, ListLiteral(D(1), n)));
        var alphabet = RangePrime(D(3), Subtract(n, D(3)));
        var body = And(Equal(pi, word),
            And(Call("Perm", sigma, alphabet),
                new Formula.Not(Call("Contains", sigma, ListLiteral(D(2), D(1), D(3))))));
        return Disp(All([Bound("n", Naturals()), Bound("pi", Word())],
            Iff(Call("LemmaForm", n, pi), Some([Bound("sigma", Word())], body))));
    }

    private static Formula ClaimFormula()
    {
        var n = Id("n");
        var pi = Id("pi");
        var permutation = Call("Perm", pi, RangePrime(D(1), n));
        var sorts = Call("TakesSorts", pi, Subtract(Multiply(D(2), n), D(5)));
        var equivalence = Iff(sorts, Call("LemmaForm", n, pi));
        var body = All([Bound("n", Naturals())],
            Implies(AtMost(D(3), n),
                All([Bound("pi", Word())], Implies(permutation, equivalence))));
        return Disp(Iff(Id("claim"), Parenthesized(body)));
    }

    private static Formula ResultFormula() => Disp(new Formula.Not(Id("claim")));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Word() => Call("List", Naturals());
    private static Formula PatternList() => Call("List", Word());
    private static Formula EmptyList() => Seq(OpenBracket, CloseBracket);
    private static Formula ListLiteral(params Formula[] values) =>
        Seq(OpenBracket, Joined(values), CloseBracket);
    private static Formula Joined(Formula[] values)
    {
        var items = new List<Formula>();
        foreach (var value in values)
        {
            if (items.Count > 0) items.AddRange([Comma, Sp]);
            items.Add(value);
        }
        return Seq([.. items]);
    }

    private static Formula Cons(Formula head, Formula tail) => Call("cons", head, tail);
    private static Formula Pair(Formula first, Formula second) =>
        Parenthesized(Seq(first, Comma, Sp, second));
    private static Formula Length(Formula value) => Call("length", value);
    private static Formula RangePrime(Formula start, Formula length) =>
        new Formula.Apply(Seq(Id("range"), Apos), [start, length]);
    private static Formula Iterate(Formula count, Formula word) =>
        Call("iterate", Call("compose", Id("s"), Id("t")), count, word);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Some(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And,
            Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies,
            Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff,
            Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
