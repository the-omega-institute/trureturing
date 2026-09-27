using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class CrosswordPermutationGridRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CrosswordPermutationGridRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lewis2026crossword");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The permutation 1,6,3,7,0,5,2,4 on zero-based indices gives a grid with 155 complete rook placements.",
        H("A Permutation Grid with 155 Rook Placements"),
        Blocks(
            Node("decidable-across", "Decidable across relation", "instDecidableRelCellSameAcross", DecidableFormula(true),
                "The finite horizontal interval condition makes the across relation decidable.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("decidable-down", "Decidable down relation", "instDecidableRelCellSameDown", DecidableFormula(false),
                "The finite vertical interval condition makes the down relation decidable.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("permutation-grid", "Permutation grid", "permGrid", PermGridFormula(),
                "The black cells form the permutation matrix; every other cell is white.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Asserted permutation-grid counts", "claim", ClaimFormula(),
                "The asserted attainable positive counts exclude four, twelve, and every number congruent to three modulo four.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("word-data", "Across classes and down labels", "WordData", WordDataFormula(),
                "A word description consists of nonempty across classes partitioning the white cells, down labels, and their image. Common across classes and equal down labels coincide with the two word relations.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("word-matching", "Perfect matching by cells", "IsWordMatching", WordMatchingFormula(),
                "A matching chooses exactly one cell of each across class and exactly one representative of every down label, with all chosen cells white.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("rook-placement-iff-word-matching", "Placements and word matchings", "rookPlacement_iff_wordMatching", RookMatchingFormula(),
                "For any exact word description, complete rook placements are precisely the perfect matchings represented by cells.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("matching-count", "Recursive matching count", "matchingCount", MatchingCountFormula(),
                "Branch over the cells of the next across word, reject used down labels, and sum the counts of the remaining words. The empty list contributes one exactly when the used labels equal the target.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("matching-sets", "Recursive matching sets", "matchingSets", MatchingSetsFormula(),
                "The same recursion forms cell sets by inserting the chosen cell into each set of the corresponding remaining branch.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("word-union", "Union of word cells", "wordUnion", WordUnionFormula(),
                "The union of an empty word list is empty; adding a first word adjoins all its cells.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("disjoint-words", "Disjoint word classes", "DisjointWords", DisjointWordsFormula(),
                "The first word is disjoint from the union of the remaining words, whose classes are recursively disjoint.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("set-matching-spec", "Partial matching conditions", "SetMatchingSpec", SetMatchingFormula(),
                "A partial matching stays inside the word union, meets each word once, uses distinct unused labels, and completes the target when combined with the already used labels.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("set-matching-cons", "Removing the first chosen cell", "setMatchingSpec_cons_iff", ConsSpecFormula(),
                "When the first word is disjoint from the remaining union, a partial matching is equivalent to choosing its cell and erasing that cell for the remaining matching.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("matching-sets-subset", "Generated cells stay in the words", "matchingSets_subset", MatchingSubsetFormula(),
                "Every recursively generated cell set is a subset of the union of its word classes.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("matching-count-card", "Counting the generated sets", "matchingCount_eq_card_sets", MatchingCardFormula(),
                "For disjoint word classes, the recursive count is the cardinality of the recursively generated cell sets.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("matching-sets-iff-spec", "Exact partial-matching enumeration", "matchingSets_iff_spec", MatchingSpecFormula(),
                "For disjoint word classes, the recursion generates exactly the cell sets satisfying the partial matching conditions.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("witness", "Concrete permutation and inverse", "witness", WitnessFormula(),
                "The permutation has values 1,6,3,7,0,5,2,4 and inverse values 4,0,6,2,7,5,1,3 on zero-based indices.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("row-run", "Concrete row interval", "rowRun", RowRunFormula(),
                "A row interval contains exactly the cells with the specified row and columns between the inclusive endpoints.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("witness-across", "Fourteen across words", "witnessAcross", WitnessAcrossFormula(),
                "The listed row intervals are the fourteen maximal across words of the concrete permutation grid.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("witness-down-id", "Fourteen down-word labels", "witnessDownId", WitnessDownFormula(),
                "Each column is labelled on the white runs above and below its black cell; the two boundary black cells leave just one white run in their columns.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("witness-matching-count", "The matching count is 155", "witness_matchingCount", Disp(Eq(Call("matchingCount", F.Id("witnessAcross"), F.Id("witnessDownId"), Call("range", D(1, 4)), Empty()), D(1, 5, 5))),
                "Starting with no used labels and target labels zero through thirteen, the concrete word recursion counts 155 matchings.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("witness-data", "Exact words of the concrete grid", "witnessData", WitnessDataFormula(),
                "The concrete across intervals and down labels satisfy all word-description conditions for the white cells of the permutation grid.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "The asserted count criterion is false", "result", Disp(new Formula.Not(F.Id("claim"))),
                "The concrete grid has 155 complete rook placements, and 155 is congruent to three modulo four, contradicting the asserted criterion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("lewis-won-permutation-grid-counts-refutation"), ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(Formula body, params (string Name, Formula Domain)[] variables)
    {
        for (var i = variables.Length - 1; i >= 0; i--)
            body = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variables[i].Name), variables[i].Domain, body);
        return body;
    }
    private static Formula Ex(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Unique(string name, Formula domain, Formula predicate) =>
        Seq(F.Exists, Sp, Bang, Sp, F.Id(name), Sp, InMacro, Sp, domain, Comma, Sp, predicate);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula SubsetOf(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.SubsetOf, b);
    private static Formula Union(Formula a, Formula b) => Seq(a, Sp, Cup, Sp, b);
    private static Formula Empty() => new Formula.SetLiteral([]);
    private static Formula Nil() => Seq(OpenBracket, CloseBracket);
    private static Formula Cons(Formula a, Formula rest) => Seq(a, Sp, Colon, Colon, Sp, rest);
    private static Formula List(params Formula[] items)
    {
        var parts = new System.Collections.Generic.List<Formula> { OpenBracket };
        for (var i = 0; i < items.Length; i++)
        {
            if (i != 0) { parts.Add(Comma); parts.Add(Sp); }
            parts.Add(items[i]);
        }
        parts.Add(CloseBracket);
        return Seq([.. parts]);
    }
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Cell(Formula n) => Call("Cell", n);
    private static Formula Finset(Formula a) => Call("Finset", a);
    private static Formula Words(Formula a) => Call("List", Finset(a));
    private static Formula Perm(Formula n) => Call("EquivPerm", Fin(n));
    private static Formula Row(Formula c) => Call("val", Seq(c, Dot, D(1)));
    private static Formula Col(Formula c) => Call("val", Seq(c, Dot, D(2)));
    private static Formula Field(Formula d, string name) => Seq(d, Dot, F.Id(name));
    private static Formula Down(Formula d, Formula c) => Call("downId", d, c);
    private static Formula Image(Formula id, Formula r) => Call("image", id, r);
    private static Formula If(Formula p, Formula a, Formula b) => Call("if", p, a, b);
    private static Formula Set(string name, Formula domain, Formula predicate) =>
        Seq(OpenBrace, Sp, F.Id(name), Sp, InMacro, Sp, domain, Sp, Bar, Sp, predicate, CloseBrace, Sp);
    private static Formula Generic(Formula body, bool decidable, params (string Name, Formula Domain)[] variables)
    {
        body = All(body, variables);
        if (decidable) body = All(body, ("e", Call("DecidableEq", F.Id("alpha"))));
        return Disp(All(body, ("alpha", F.Id("Type"))));
    }

    private static Formula DecidableFormula(bool across)
    {
        var n = F.Id("n"); var w = F.Id("W");
        return Disp(All(Call("DecidableRel", Call(across ? "SameAcross" : "SameDown", w)),
            ("n", Nat()), ("W", Finset(Cell(n)))));
    }

    private static Formula PermGridFormula()
    {
        var n = F.Id("n"); var w = F.Id("w"); var c = F.Id("c");
        return Disp(All(Eq(Call("permGrid", w), Set("c", Cell(n),
            Ne(Call("w", Seq(c, Dot, D(1))), Seq(c, Dot, D(2))))), ("n", Nat()), ("w", Perm(n))));
    }

    private static Formula ClaimFormula()
    {
        var r = F.Id("r"); var n = F.Id("n"); var w = F.Id("w");
        var attained = Ex("n", Nat(), Ex("w", Perm(n), Eq(Call("rookCount", Call("permGrid", w)), r)));
        var criterion = And(Ne(r, D(4)), Ne(r, D(1, 2)), Ne(new Formula.Modulo(r, D(4)), D(3)));
        return Disp(Iff(F.Id("claim"), All(Imp(Lt(D(0), r), Iff(attained, criterion)), ("r", Nat()))));
    }

    private static Formula WordDataFormula()
    {
        var n = F.Id("n"); var w = F.Id("W"); var across = F.Id("across");
        var id = F.Id("downId"); var ids = F.Id("downIds"); var a = F.Id("A");
        var c = F.Id("c"); var d = F.Id("d");
        var constraints = And(
            All(Imp(Mem(a, across), SubsetOf(a, w)), ("A", Finset(Cell(n)))),
            All(Imp(Mem(a, across), Call("Nonempty", a)), ("A", Finset(Cell(n)))),
            All(Imp(Mem(c, w), Unique("A", Finset(Cell(n)), And(Mem(a, across), Mem(c, a)))), ("c", Cell(n))),
            All(Imp(Mem(c, w), All(Imp(Mem(d, w), Iff(Call("SameAcross", w, c, d),
                Ex("A", Finset(Cell(n)), And(Mem(a, across), Mem(c, a), Mem(d, a))))), ("d", Cell(n)))), ("c", Cell(n))),
            All(Imp(Mem(c, w), All(Imp(Mem(d, w), Iff(Call("SameDown", w, c, d),
                Eq(Call("downId", c), Call("downId", d)))), ("d", Cell(n)))), ("c", Cell(n))),
            Eq(Image(id, w), ids));
        var record = Seq(OpenBrace, Sp, across, Colon, Sp, Words(Cell(n)), Semi, Sp,
            id, Colon, Sp, new Formula.TypeArrow(Cell(n), Nat()), Semi, Sp,
            ids, Colon, Sp, Finset(Nat()), Sp, Bar, Sp, constraints, CloseBrace, Sp);
        return Disp(All(Eq(Call("WordData", n, w), record), ("n", Nat()), ("W", Finset(Cell(n)))));
    }

    private static Formula WordMatchingFormula()
    {
        var n = F.Id("n"); var w = F.Id("W"); var data = F.Id("D"); var r = F.Id("R");
        var a = F.Id("A"); var c = F.Id("c"); var d = F.Id("d");
        var body = And(SubsetOf(r, w),
            All(Imp(Mem(a, Field(data, "across")), Unique("c", Cell(n), And(Mem(c, r), Mem(c, a)))), ("A", Finset(Cell(n)))),
            All(Imp(Mem(c, r), All(Imp(Mem(d, r), Imp(Ne(c, d), Ne(Down(data, c), Down(data, d)))), ("d", Cell(n)))), ("c", Cell(n))),
            Eq(Image(Field(data, "downId"), r), Field(data, "downIds")));
        return Disp(All(Iff(Call("IsWordMatching", data, r), body), ("n", Nat()),
            ("W", Finset(Cell(n))), ("D", Call("WordData", n, w)), ("R", Finset(Cell(n)))));
    }

    private static Formula RookMatchingFormula()
    {
        var n = F.Id("n"); var w = F.Id("W"); var data = F.Id("D"); var r = F.Id("R");
        return Disp(All(Iff(Call("IsRookPlacement", w, r), Call("IsWordMatching", data, r)),
            ("n", Nat()), ("W", Finset(Cell(n))), ("D", Call("WordData", n, w)), ("R", Finset(Cell(n)))));
    }

    private static Formula MatchingCountFormula()
    {
        var alpha = F.Id("alpha"); var a = F.Id("A"); var rest = F.Id("rest");
        var id = F.Id("id"); var target = F.Id("target"); var used = F.Id("used"); var c = F.Id("c");
        var branch = If(Mem(Call("id", c), used), D(0), Call("matchingCount", rest, id, target, Call("insert", Call("id", c), used)));
        var recurrence = And(Eq(Call("matchingCount", Nil(), id, target, used), If(Eq(used, target), D(1), D(0))),
            Eq(Call("matchingCount", Cons(a, rest), id, target, used), Seq(Sum, Sp, c, Sp, InMacro, Sp, a, Sp, branch)));
        return Generic(recurrence, false, ("A", Finset(alpha)), ("rest", Words(alpha)),
            ("id", new Formula.TypeArrow(alpha, Nat())), ("target", Finset(Nat())), ("used", Finset(Nat())));
    }

    private static Formula MatchingSetsFormula()
    {
        var alpha = F.Id("alpha"); var a = F.Id("A"); var rest = F.Id("rest");
        var id = F.Id("id"); var target = F.Id("target"); var used = F.Id("used"); var c = F.Id("c");
        var branch = If(Mem(Call("id", c), used), Empty(),
            Image(Call("insert", c), Call("matchingSets", rest, id, target, Call("insert", Call("id", c), used))));
        var lambda = Seq(LambdaLower, Sp, c, Colon, Sp, alpha, Dot, Sp, branch);
        var recurrence = And(Eq(Call("matchingSets", Nil(), id, target, used), If(Eq(used, target), new Formula.SetLiteral([Empty()]), Empty())),
            Eq(Call("matchingSets", Cons(a, rest), id, target, used), Call("biUnion", a, lambda)));
        return Generic(recurrence, true, ("A", Finset(alpha)), ("rest", Words(alpha)),
            ("id", new Formula.TypeArrow(alpha, Nat())), ("target", Finset(Nat())), ("used", Finset(Nat())));
    }

    private static Formula WordUnionFormula()
    {
        var alpha = F.Id("alpha"); var a = F.Id("A"); var rest = F.Id("rest");
        return Generic(And(Eq(Call("wordUnion", Nil()), Empty()),
            Eq(Call("wordUnion", Cons(a, rest)), Union(a, Call("wordUnion", rest)))), true,
            ("A", Finset(alpha)), ("rest", Words(alpha)));
    }

    private static Formula DisjointWordsFormula()
    {
        var alpha = F.Id("alpha"); var a = F.Id("A"); var rest = F.Id("rest");
        return Generic(And(Iff(Call("DisjointWords", Nil()), F.Id("True")),
            Iff(Call("DisjointWords", Cons(a, rest)), And(Call("Disjoint", a, Call("wordUnion", rest)), Call("DisjointWords", rest)))),
            true, ("A", Finset(alpha)), ("rest", Words(alpha)));
    }

    private static Formula SetMatchingFormula()
    {
        var alpha = F.Id("alpha"); var words = F.Id("words"); var id = F.Id("id");
        var target = F.Id("target"); var used = F.Id("used"); var r = F.Id("R");
        var a = F.Id("A"); var c = F.Id("c"); var d = F.Id("d");
        var conditions = And(SubsetOf(r, Call("wordUnion", words)),
            All(Imp(Mem(a, words), Unique("c", alpha, And(Mem(c, r), Mem(c, a)))), ("A", Finset(alpha))),
            All(Imp(Mem(c, r), All(Imp(Mem(d, r), Imp(Ne(c, d), Ne(Call("id", c), Call("id", d)))), ("d", alpha))), ("c", alpha)),
            All(Imp(Mem(c, r), new Formula.Not(Mem(Call("id", c), used))), ("c", alpha)), Eq(Union(Image(id, r), used), target));
        return Generic(Iff(Call("SetMatchingSpec", words, id, target, used, r), conditions), true,
            ("words", Words(alpha)), ("id", new Formula.TypeArrow(alpha, Nat())),
            ("target", Finset(Nat())), ("used", Finset(Nat())), ("R", Finset(alpha)));
    }

    private static Formula ConsSpecFormula()
    {
        var alpha = F.Id("alpha"); var a = F.Id("A"); var rest = F.Id("rest");
        var id = F.Id("id"); var target = F.Id("target"); var used = F.Id("used"); var r = F.Id("R"); var c = F.Id("c");
        var tail = Ex("c", alpha, And(Mem(c, a), Mem(c, r), new Formula.Not(Mem(Call("id", c), used)),
            Call("SetMatchingSpec", rest, id, target, Call("insert", Call("id", c), used), Call("erase", r, c))));
        return Generic(Imp(Call("Disjoint", a, Call("wordUnion", rest)),
            Iff(Call("SetMatchingSpec", Cons(a, rest), id, target, used, r), tail)), true,
            ("A", Finset(alpha)), ("rest", Words(alpha)), ("id", new Formula.TypeArrow(alpha, Nat())),
            ("target", Finset(Nat())), ("used", Finset(Nat())), ("R", Finset(alpha)));
    }

    private static Formula MatchingSubsetFormula()
    {
        var alpha = F.Id("alpha"); var words = F.Id("words"); var id = F.Id("id");
        var target = F.Id("target"); var used = F.Id("used"); var r = F.Id("R");
        return Generic(Imp(Mem(r, Call("matchingSets", words, id, target, used)), SubsetOf(r, Call("wordUnion", words))), true,
            ("words", Words(alpha)), ("id", new Formula.TypeArrow(alpha, Nat())),
            ("target", Finset(Nat())), ("used", Finset(Nat())), ("R", Finset(alpha)));
    }

    private static Formula MatchingCardFormula()
    {
        var alpha = F.Id("alpha"); var words = F.Id("words"); var id = F.Id("id"); var target = F.Id("target"); var used = F.Id("used");
        return Generic(Imp(Call("DisjointWords", words), Eq(Call("matchingCount", words, id, target, used),
            Call("card", Call("matchingSets", words, id, target, used)))), true,
            ("words", Words(alpha)), ("id", new Formula.TypeArrow(alpha, Nat())), ("target", Finset(Nat())), ("used", Finset(Nat())));
    }

    private static Formula MatchingSpecFormula()
    {
        var alpha = F.Id("alpha"); var words = F.Id("words"); var id = F.Id("id");
        var target = F.Id("target"); var used = F.Id("used"); var r = F.Id("R");
        return Generic(Imp(Call("DisjointWords", words), Iff(Mem(r, Call("matchingSets", words, id, target, used)),
            Call("SetMatchingSpec", words, id, target, used, r))), true,
            ("words", Words(alpha)), ("id", new Formula.TypeArrow(alpha, Nat())),
            ("target", Finset(Nat())), ("used", Finset(Nat())), ("R", Finset(alpha)));
    }

    private static Formula WitnessFormula()
    {
        var i = F.Id("i");
        return Disp(All(And(
            Eq(Call("val", Call("witness", i)), Call("nth", List(D(1), D(6), D(3), D(7), D(0), D(5), D(2), D(4)), Call("val", i))),
            Eq(Call("val", Call("invFun", F.Id("witness"), i)), Call("nth", List(D(4), D(0), D(6), D(2), D(7), D(5), D(1), D(3)), Call("val", i)))),
            ("i", Fin(D(8)))));
    }

    private static Formula RowRunFormula()
    {
        var i = F.Id("i"); var lo = F.Id("lo"); var hi = F.Id("hi"); var c = F.Id("c");
        return Disp(All(Eq(Call("rowRun", i, lo, hi), Set("c", Cell(D(8)), And(Eq(Row(c), i), Le(lo, Col(c)), Le(Col(c), hi)))),
            ("i", Nat()), ("lo", Nat()), ("hi", Nat())));
    }

    private static Formula WitnessAcrossFormula() => Disp(Eq(F.Id("witnessAcross"), List(
        Call("rowRun", D(0), D(0), D(0)), Call("rowRun", D(0), D(2), D(7)),
        Call("rowRun", D(1), D(0), D(5)), Call("rowRun", D(1), D(7), D(7)),
        Call("rowRun", D(2), D(0), D(2)), Call("rowRun", D(2), D(4), D(7)),
        Call("rowRun", D(3), D(0), D(6)), Call("rowRun", D(4), D(1), D(7)),
        Call("rowRun", D(5), D(0), D(4)), Call("rowRun", D(5), D(6), D(7)),
        Call("rowRun", D(6), D(0), D(1)), Call("rowRun", D(6), D(3), D(7)),
        Call("rowRun", D(7), D(0), D(3)), Call("rowRun", D(7), D(5), D(7)))));

    private static Formula WitnessDownFormula()
    {
        var c = F.Id("c"); var a = Row(c); var b = Col(c);
        var value = If(Le(a, D(2)), D(1, 2), D(1, 3));
        value = If(Eq(b, D(6)), If(Eq(a, D(0)), D(1, 0), D(1, 1)), value);
        value = If(Eq(b, D(5)), If(Le(a, D(4)), D(8), D(9)), value);
        value = If(Eq(b, D(4)), D(7), value);
        value = If(Eq(b, D(3)), If(Le(a, D(1)), D(5), D(6)), value);
        value = If(Eq(b, D(2)), If(Le(a, D(5)), D(3), D(4)), value);
        value = If(Eq(b, D(1)), D(2), value);
        value = If(Eq(b, D(0)), If(Le(a, D(3)), D(0), D(1)), value);
        return Disp(All(Eq(Call("witnessDownId", c), value), ("c", Cell(D(8)))));
    }

    private static Formula WitnessDataFormula() => Disp(And(
        Seq(F.Id("witnessData"), Colon, Sp, Call("WordData", D(8), Call("permGrid", F.Id("witness")))),
        Eq(Field(F.Id("witnessData"), "across"), F.Id("witnessAcross")),
        Eq(Field(F.Id("witnessData"), "downId"), F.Id("witnessDownId")),
        Eq(Field(F.Id("witnessData"), "downIds"), Call("range", D(1, 4)))));
}
