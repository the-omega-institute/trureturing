using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Carry;

internal sealed class ListInversionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/Carry/ListInversions.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local list replacements have inversion costs bounded by surrounding occurrence counts.",
        H("List Inversions and Local Replacement Bounds"),
        Blocks(
            Paragraph(Text(
                "All entries are natural numbers, and P and S are arbitrary surrounding lists. "
                + "The notation ++ denotes list concatenation, count(L, x) counts occurrences "
                + "of x in L, and every map, filter, and sum is a list operation. Repeated "
                + "entries retain their multiplicity. Subtraction is natural-number subtraction.")),
            Node("inv", "Count inversions by head recursion", InversionFormula(),
                "An inversion is a pair of positions p < q whose entries satisfy s[p] > s[q]. "
                + "The empty list has no inversions. For a head x and tail xs, the inversions "
                + "inside xs are retained, and each tail entry strictly smaller than x "
                + "contributes one inversion with the head.",
                DescribeRole.Definition),
            Node("inv_window", "Separate the window from its surroundings", WindowFormula(),
                "For arbitrary natural-number lists P, W, and S, the parenthesized term "
                + "counts inversions inside P, inside S, and from P to S; it is independent "
                + "of W. The remaining terms count inversions inside W, from P to W, and "
                + "from W to S. Each occurrence of a window entry contributes separately. "
                + "The proof inducts on the prefix and interchanges the two finite list counts.",
                DescribeRole.Theorem),
            Node("inv_replace_double", "Replace a repeated entry above two", DoubleFormula(),
                "For every natural i with 2 < i, replacing [i, i] by [i - 2, i + 1] "
                + "in any surroundings increases the inversion count by at most the total "
                + "occurrences of i - 1 and i in P ++ S. The hypothesis 2 < i is part of "
                + "the statement. Splitting the crossing counts at successive thresholds "
                + "isolates these occurrence counts; monotonicity bounds the other terms.",
                DescribeRole.Theorem),
            Node("inv_replace_adjacent", "Merge consecutive entries", AdjacentFormula(),
                "For every natural a, replacing [a, a + 1] by [a + 2] increases the "
                + "inversion count by at most the occurrences of a + 1 in P ++ S. There "
                + "is no positivity assumption on a. The new suffix threshold adds exactly "
                + "the occurrences of a + 1 in S, while the prefix contribution is bounded "
                + "by the previous crossing counts.",
                DescribeRole.Theorem),
            Node("inv_replace_ones", "Merge two ones", OnesFormula(),
                "Replacing [1, 1] by [2] in arbitrary natural-number surroundings increases "
                + "the inversion count by at most the occurrences of 1 in P ++ S. Zeros "
                + "in the suffix are allowed: their contribution remains in the count of "
                + "entries below 1. The threshold from 1 to 2 adds only suffix ones.",
                DescribeRole.Theorem),
            Node("inv_replace_twos", "Replace two twos", TwosFormula(),
                "Replacing [2, 2] by [1, 3] in arbitrary natural-number surroundings "
                + "increases the inversion count by at most the occurrences of 2 in P ++ S. "
                + "The prefix threshold from 2 to 1 and the suffix threshold from 2 to 3 "
                + "contribute the prefix and suffix twos, respectively; the other crossing "
                + "terms are bounded by monotonicity.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("list-inversions-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula InversionFormula()
    {
        var x = F.Id("x");
        var xs = F.Id("xs");
        var count = Call("countP", xs,
            Lambda(F.Id("y"), Call("decide", Less(F.Id("y"), x))));
        return Disp(Seq(
            Equal(Inv(Seq(OpenBracket, CloseBracket)), D(0)), Sp, Land, Sp,
            Universal("x", Naturals(), Universal("xs", Lists(),
                Equal(Inv(Seq(x, Sp, Colon, Colon, Sp, xs)), Add(Inv(xs), count))))));
    }

    private static Formula WindowFormula()
    {
        var p = F.Id("P");
        var w = F.Id("W");
        var s = F.Id("S");
        var outside = Parenthesized(Add(Add(Inv(p), Inv(s)),
            ListSum(p, "p", FilterLength(s, "q", Less(F.Id("q"), F.Id("p"))))));
        var before = ListSum(w, "x", FilterLength(p, "p", Less(F.Id("x"), F.Id("p"))));
        var after = ListSum(w, "x", FilterLength(s, "q", Less(F.Id("q"), F.Id("x"))));
        return Disp(Universal("P", Lists(), Universal("W", Lists(), Universal("S", Lists(),
            Equal(Inv(Window(w)), Add(Add(Add(outside, Inv(w)), before), after))))));
    }

    private static Formula DoubleFormula()
    {
        var i = F.Id("i");
        var cost = Parenthesized(Add(OutsideCount(Subtract(i, D(1))), OutsideCount(i)));
        return Disp(Surroundings(Universal("i", Naturals(), Seq(
            Less(D(2), i), Sp, Rightarrow, Sp,
            Replacement(Pair(i, i), Pair(Subtract(i, D(2)), Add(i, D(1))), cost)))));
    }

    private static Formula AdjacentFormula()
    {
        var a = F.Id("a");
        return Disp(Surroundings(Universal("a", Naturals(),
            Replacement(Pair(a, Add(a, D(1))), Single(Add(a, D(2))),
                OutsideCount(Add(a, D(1)))))));
    }

    private static Formula OnesFormula() => Disp(Surroundings(
        Replacement(Pair(D(1), D(1)), Single(D(2)), OutsideCount(D(1)))));

    private static Formula TwosFormula() => Disp(Surroundings(
        Replacement(Pair(D(2), D(2)), Pair(D(1), D(3)), OutsideCount(D(2)))));

    private static Formula Replacement(Formula before, Formula after, Formula cost) =>
        new Formula.Relation(Inv(Window(after)), FormulaRelationOperator.LessThanOrEqual,
            Add(Inv(Window(before)), cost));
    private static Formula Surroundings(Formula body) =>
        Universal("P", Lists(), Universal("S", Lists(), body));
    private static Formula Window(Formula entries) => Append(Append(F.Id("P"), entries), F.Id("S"));
    private static Formula OutsideCount(Formula entry) => Call("count", Append(F.Id("P"), F.Id("S")), entry);
    private static Formula Inv(Formula list) => Call("inv", list);
    private static Formula ListSum(Formula list, string variable, Formula body) =>
        Call("sum", Call("map", Lambda(F.Id(variable), body), list));
    private static Formula FilterLength(Formula list, string variable, Formula predicate) =>
        Call("length", Call("filter", Lambda(F.Id(variable), Call("decide", predicate)), list));
    private static Formula Naturals() => F.Id("Nat");
    private static Formula Lists() => Call("List", Naturals());
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Single(Formula entry) => Seq(OpenBracket, entry, CloseBracket);
    private static Formula Pair(Formula first, Formula second) =>
        Seq(OpenBracket, first, Comma, Sp, second, CloseBracket);
    private static Formula Append(Formula left, Formula right) => Seq(left, Sp, Plus, Plus, Sp, right);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Lambda(Formula variable, Formula body) =>
        Parenthesized(Seq(variable, Sp, Mapsto, Sp, body));
    private static Formula Universal(string variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, F.Id(variable), Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
}
