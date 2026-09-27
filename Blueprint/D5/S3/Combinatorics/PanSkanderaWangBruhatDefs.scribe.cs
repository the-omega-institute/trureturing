using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class PanSkanderaWangBruhatDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/pan2026permanental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Definitions of the Pan-Skandera-Wang map, its source family, and its Bruhat claim.",
        H("Pan-Skandera-Wang Bruhat Definitions"),
        Blocks(
            Node("rank", "Rank tableau count", "rank", RankFormula(),
                "The rank counts entries at least q among the first p positions.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("is-perm", "Permutation predicate", "IsPerm", IsPermFormula(),
                "A word is a permutation when it is a rearrangement of the interval from one through n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bruhat-le", "Bruhat tableau order", "BruhatLE", BruhatLEFormula(),
                "The strong Bruhat order is given by the tableau criterion of Björner and Brenti, Theorem 2.1.5.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a-family", "The source family A", "A", AFormula(),
                "The first half of the word permutes the initial interval while the whole word is a permutation.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ru", "Reverse-complement map", "RU", RuFormula(),
                "The reverse-complement map reverses a word and replaces each value v by n plus one minus v.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("swap-pairs", "Pair swapping", "swapPairs", SwapPairsFormula(),
                "Pair swapping exchanges adjacent entries and leaves a final unpaired entry fixed.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("inss", "Suffix-swapping insertion", "inss", InssFormula(),
                "The operation inserts the new maximum at position q and swaps successive pairs in the suffix.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("f4", "Base map", "f4", F4Formula(),
                "The base map is specified on the four words of size four and fixes every other input at that size.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("f", "Recursive Pan-Skandera-Wang map", "f", FFormula(),
                "The recursive map uses the base cases, the position of the maximum, insertion, and reverse-complementation according to parity.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Bruhat monotonicity claim", "claim", ClaimFormula(),
                "For every size at least four, each source word is below its image in the strong Bruhat order.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role);

    private static Formula RankFormula() => Disp(ForAllMany(
        [Bound("x", ListType()), Bound("p", Naturals()), Bound("q", Naturals())],
        Equal(Call("rank", X(), P(), Q()),
            Call("countGE", Q(), Call("take", X(), P())))));

    private static Formula IsPermFormula() => Disp(ForAllMany(
        [Bound("n", Naturals()), Bound("x", ListType())],
        Iff(Call("IsPerm", N(), X()),
            Call("Perm", X(), Call("rangePrime", D(1), N())))));

    private static Formula BruhatLEFormula() => Disp(ForAllMany(
        [Bound("n", Naturals()), Bound("x", ListType()), Bound("y", ListType())],
        Iff(Call("BruhatLE", N(), X(), Y()),
            And(Call("IsPerm", N(), X()), Call("IsPerm", N(), Y()),
                ForAllMany([Bound("p", Naturals()), Bound("q", Naturals())],
                    LessEqual(Call("rank", X(), P(), Q()), Call("rank", Y(), P(), Q())))))));

    private static Formula AFormula() => Disp(ForAllMany(
        [Bound("n", Naturals()), Bound("w", ListType())],
        Iff(Call("A", N(), W()),
            And(Call("IsPerm", N(), W()),
                Call("Perm", Call("take", W(), Call("floorHalf", N())),
                    Call("rangePrime", D(1), Call("floorHalf", N())))))));

    private static Formula RuFormula() => Disp(ForAllMany(
        [Bound("n", Naturals()), Bound("w", ListType())],
        Equal(Call("RU", N(), W()),
            Call("map", Seq(Lambda, Sp, F.Id("v"), Sp, Mapsto, Sp,
                Subtract(Add(N(), D(1)), F.Id("v"))), Call("reverse", W())))));

    private static Formula SwapPairsFormula() => Disp(And(
        Equal(Call("swapPairs", EmptyList()), EmptyList()),
        Equal(Call("swapPairs", Singleton(F.Id("a"))), Singleton(F.Id("a"))),
        ForAllMany([Bound("a", Naturals()), Bound("b", Naturals()), Bound("t", ListType())],
            Equal(Call("swapPairs", Cons(F.Id("a"), Cons(F.Id("b"), F.Id("t")))),
                Cons(F.Id("b"), Cons(F.Id("a"), Call("swapPairs", F.Id("t"))))))));

    private static Formula InssFormula() => Disp(ForAllMany(
        [Bound("q", Naturals()), Bound("w", ListType())],
        Equal(Call("inss", Q(), W()),
            Call("append", Call("take", W(), Subtract(Q(), D(1))),
                Cons(Add(Call("length", W()), D(1)),
                    Call("swapPairs", Call("drop", W(), Subtract(Q(), D(1)))))))));

    private static Formula F4Formula() => Disp(ForAll("w", ListType(),
        Equal(Call("f4", F.Id("w")),
            If(Equal(F.Id("w"), ListOf(1, 2, 3, 4)), ListOf(1, 2, 3, 4),
                If(Equal(F.Id("w"), ListOf(1, 2, 4, 3)), ListOf(1, 4, 3, 2),
                    If(Equal(F.Id("w"), ListOf(2, 1, 3, 4)), ListOf(3, 2, 1, 4),
                        If(Equal(F.Id("w"), ListOf(2, 1, 4, 3)), ListOf(3, 4, 1, 2), F.Id("w"))))))));

    private static Formula FFormula()
    {
        var m = F.Id("m");
        var w = F.Id("w");
        var max = Add(m, D(1));
        var p = Add(Call("idxOf", w, max), D(1));
        var a = Call("eraseIdx", w, Call("idxOf", w, max));
        var even = Call("inss",
            Subtract(Multiply(D(2), Subtract(p, Call("floorHalf", m))), D(1)),
            Call("f", m, a));
        var odd = Call("inss",
            Multiply(D(2), Subtract(Subtract(p, Call("floorHalf", m)), D(1))),
            Call("RU", m, Call("f", m, Call("RU", m, a))));
        var step = If(Equal(Call("mod", m, D(2)), D(0)), even, odd);
        return Disp(And(
            ForAll("w", ListType(), Equal(Call("f", D(0), w), w)),
            ForAllMany([Bound("m", Naturals()), Bound("w", ListType())],
                Equal(Call("f", Add(m, D(1)), w),
                    If(LessEqual(Add(m, D(1)), D(4)), Call("f4", w), step)))));
    }

    private static Formula ClaimFormula() => Disp(ForAll("n", Naturals(),
        Implies(LessEqual(D(4), F.Id("n")),
            ForAll("w", ListType(),
                Implies(Call("A", F.Id("n"), F.Id("w")),
                    Call("BruhatLE", F.Id("n"), F.Id("w"), Call("f", F.Id("n"), F.Id("w"))))))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula X() => F.Id("x");
    private static Formula P() => F.Id("p");
    private static Formula Q() => F.Id("q");
    private static Formula N() => F.Id("n");
    private static Formula W() => F.Id("w");
    private static Formula Y() => F.Id("y");
    private static Formula Naturals() => Seq(Mathbb, Sp, Grp(F.Id("N")));
    private static Formula ListType() => Call("List", Naturals());
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula ForAllMany(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula If(Formula condition, Formula whenTrue, Formula whenFalse) =>
        Call("if", condition, whenTrue, whenFalse);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula EmptyList() => Call("nil");
    private static Formula Singleton(Formula value) => Call("singleton", value);
    private static Formula Cons(Formula head, Formula tail) => Call("cons", head, tail);
    private static Formula ListOf(params byte[] values)
    {
        var items = new Formula[values.Length];
        for (var index = 0; index < values.Length; index++) items[index] = D(values[index]);
        return Call("list", items);
    }
}
