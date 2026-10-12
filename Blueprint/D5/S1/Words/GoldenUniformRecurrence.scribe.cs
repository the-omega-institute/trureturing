using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class GoldenUniformRecurrenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Give an explicit linear window in which every finite golden-word factor recurs.",
        H("Uniform Recurrence of the Golden Word"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("window-take-drop-is-infix"),
                DeclarationHandle.Create("D5/S1/Words/GoldenUniformRecurrence.take_drop_isInfix"),
                H("Every truncated suffix is an infix"), StatementSource.FromAuthor(WindowSupplier("take_drop_isInfix")),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every type alpha, list l and natural p,n, taking n entries after dropping p entries yields an infix of l. No length assumption is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("window-exists-flat-map-block"),
                DeclarationHandle.Create("D5/S1/Words/GoldenUniformRecurrence.exists_flatMap_block"),
                H("Locate a start inside a concatenated block"), StatementSource.FromAuthor(WindowSupplier("exists_flatMap_block")),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For arbitrary types alpha and beta, a list-valued map f, a source list l and a natural p below the concatenated image length, there are lists pre and post and a letter a with l=pre++a::post, length(flatMap(f,pre)) at most p, and p strictly below that length plus length(f(a)). Images may be empty."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("window-take-drop-append-eq-left"),
                DeclarationHandle.Create("D5/S1/Words/GoldenUniformRecurrence.take_drop_append_eq_left"),
                H("Windows contained in the left list"), StatementSource.FromAuthor(WindowSupplier("take_drop_append_eq_left")),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every type alpha, lists x,y and natural p,n with p+n at most length(x), the window obtained from x++y by dropping p entries and taking n is exactly the corresponding window of x."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-recurrence-bound"),
                DeclarationHandle.Create("D5/S1/Words/GoldenUniformRecurrence.goldenRecurrenceBound"),
                H("The recurrence window is an explicit Fibonacci quantity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a factor length n, let k be the greatest Fibonacci index with "
                    + "Fib(k) at most n, and define B(n) = 3 Fib(k+5). This bound is "
                    + "deliberately coarse; no optimality claim is made."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("uniform-recurrence-window"),
                DeclarationHandle.Create("D5/S1/Words/GoldenUniformRecurrence.golden_factor_uniformly_recurrent"),
                H("Every factor recurs wholly inside every B(n)-window"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Forall, Sp, F.Id("i"), Comma, Esc, Exists, Sp, F.Id("j"), Comma, Esc,
                                    F.Id("i"), Le, Sp, F.Id("j"), Sp, Land, Sp,
                                    F.Id("j"), Plus, F.Id("n"), Le, Sp, F.Id("i"), Plus,
                                    F.Id("B"), Open, F.Id("n"), Close, Sp, Land, Sp,
                                    F.Id("w"), Eq, Operatorname, Grp(F.Id("goldenFactor")), Open,
                                    F.Id("n"), Comma, F.Id("j"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "For every starting coordinate i and every word w occurring as a "
                                    + "length-n golden factor, there is a start j at or after i such that "
                                    + "w begins at j and ends no later than i+B(n). The proof locates w "
                                    + "inside one control supertile, then finds a complete copy of that "
                                    + "supertile after the arbitrary starting coordinate."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("linear-bound"),
                DeclarationHandle.Create("D5/S1/Words/GoldenUniformRecurrence.golden_recurrenceBound_le"),
                H("The explicit window is at most thirty-nine times the factor length"),
                StatementSource.FromAuthor(Disp(Seq(
                                    F.Id("n"), Gt, D(0), Sp, Rightarrow, Sp,
                                    F.Id("B"), Open, F.Id("n"), Close, Le, D(3, 9), F.Id("n")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "For positive n, Fib(k) is at most n and Fib(k+1) is at most 2n. "
                                    + "The identity Fib(k+5) = 3 Fib(k) + 5 Fib(k+1) therefore gives "
                                    + "B(n) at most 39n."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("direct-linear-window"),
                DeclarationHandle.Create("D5/S1/Words/GoldenUniformRecurrence.golden_factor_uniformly_recurrent_linear"),
                H("Every positive-length factor recurs in a direct 39n window"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Forall, Sp, F.Id("i"), Comma, Esc, Exists, Sp, F.Id("j"), Comma, Esc,
                                    F.Id("i"), Le, Sp, F.Id("j"), Sp, Land, Sp,
                                    F.Id("j"), Plus, F.Id("n"), Le, Sp, F.Id("i"), Plus, D(3, 9), F.Id("n"),
                                    Sp, Land, Sp, F.Id("w"), Eq,
                                    Operatorname, Grp(F.Id("goldenFactor")), Open,
                                    F.Id("n"), Comma, F.Id("j"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "Combining uniform recurrence with the coarse linear estimate removes "
                                    + "the auxiliary Fibonacci expression from the window endpoint."))),
                DescribeRole.Theorem
            )),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Words/GoldenWord")),
        ]));
    private static Formula WindowSupplier(string name)
    {
        Formula a = F.Id("alpha"), b = F.Id("beta"), l = F.Id("l"), f = F.Id("f");
        Formula p = F.Id("p"), n = F.Id("n"), x = F.Id("x"), y = F.Id("y");
        Formula pre = F.Id("pre"), letter = F.Id("a"), post = F.Id("post");
        Formula lists = WC("List", a);
        Formula Flat(Formula word) => WC("flatMap", f, word);
        Formula Len(Formula word) => WC("length", word);
        Formula Window(Formula word) => WC("take", n, WC("drop", p, word));
        Formula decomposition = WQ(l, WC("append", pre, WC("cons", letter, post)));
        Formula blockStart = Len(Flat(pre));
        Formula blockEnd = WP(blockStart, Len(new Formula.Apply(f, [letter])));
        Formula blockBounds = WB(WL(blockStart, p), WT(p, blockEnd));
        Formula blockWitness = WE("pre", lists, WE("a", a,
            WE("post", lists, WB(decomposition, blockBounds))));
        Formula locatedBlock = WA("p", WN(), WI(WT(p, Len(Flat(l))), blockWitness));
        Formula blockStatement = WA("beta", F.Id("Type"),
            WA("f", WC("Function", a, WC("List", b)), WA("l", lists, locatedBlock)));
        Formula leftWindow = WQ(Window(WC("append", x, y)), Window(x));
        Formula leftBound = WI(WL(WP(p, n), Len(x)), leftWindow);
        Formula leftStatement = WA("x", lists, WA("y", lists,
            WA("p", WN(), WA("n", WN(), leftBound))));
        Formula body = name switch
        {
            "take_drop_isInfix" => WA("l", lists, WA("p", WN(), WA("n", WN(),
                WC("IsInfix", Window(l), l)))),
            "exists_flatMap_block" => blockStatement,
            "take_drop_append_eq_left" => leftStatement,
            _ => throw new ArgumentOutOfRangeException(nameof(name)),
        };
        return F.Disp(WA("alpha", F.Id("Type"), body));
    }

    private static Formula WN() => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula WC(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula WA(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula WE(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), domain, body);
    private static Formula WQ(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula WL(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula WT(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula WP(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula WI(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula WB(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);

}
