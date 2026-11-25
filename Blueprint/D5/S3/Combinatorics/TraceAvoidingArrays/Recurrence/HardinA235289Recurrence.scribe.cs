using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence;

internal sealed class HardinA235289RecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.";
    private const string Note = "D5/L/Automata/hardin2014a235289";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hardin's common six-lag recurrence for constant-stress rectangular arrays.",
        H("Hardin's constant-stress rectangular arrays"),
        Blocks(
            Definition("Grid", "Rectangular arrays", GridDefinition(),
                "The alphabet has four entries, 0 through 3. Indices start at zero, so a grid indexed by n and k has n+1 rows and k+1 columns."),
            Definition("Legal", "The contiguous block condition", LegalDefinition(),
                "Each pair of indices selects the upper left corner of one contiguous block. Fin.castSucc preserves the index and Fin.succ increments it, both in the larger index type. The condition uses the natural absolute value of the difference of the diagonal and antidiagonal sums after casting the entries to integers."),
            Definition("T", "The literal rectangular count", CountDefinition(),
                "The cardinality counts every legal filling in its given orientation. It is viewed as an integer for the signed recurrence."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The common six-lag recurrence"),
                StatementSource.FromAuthor(Disp(RecurrenceStatement())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(
                    Paragraph(Text("OEIS A235289 proposes a common recurrence for every row and every column. The pair d gives the row and column indices of the table. Either varying index starts at seven, since the smallest lagged index in each displayed identity is positive.")),
                    Paragraph(Text("Complementing every cell on one checkerboard color converts the diagonal difference into a block sum of two or ten. Adjacent blocks share two cells. Their sums can differ by at most six, so every block has the same sum. Complementing all cells exchanges the two classes.")),
                    Paragraph(Text("For a sum-two array, the horizontal adjacent sums in successive rows alternate between a profile and its complement in two. Each profile and its complement have at most four row choices in total, since the first cell determines a row from its adjacent sums. The nonzero contributions have one-step multiplier one or two, or two-step multiplier two or three. Each contribution satisfies the displayed recurrence, and summing the contributions proves the first identity. Transposition gives the second."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static Formula GridDefinition()
    {
        var n = V("n");
        var k = V("k");
        var grid = Seq(Call("Fin", PlusOf(n, D(1))), Sp, To, Sp,
            Call("Fin", PlusOf(k, D(1))), Sp, To, Sp, Call("Fin", D(4)));
        return Dimensions(Eq(Call("Grid", n, k), grid));
    }

    private static Formula LegalDefinition()
    {
        var i = V("i");
        var j = V("j");
        var a = V("A");
        var n = V("n");
        var k = V("k");
        Formula Entry(Formula row, Formula column) =>
            Parenthesized(Seq(Call("val", App(a, row, column)), Colon, Sp, V("Int")));
        var top = App(Qualified("Fin", "castSucc"), i);
        var bottom = App(Qualified("Fin", "succ"), i);
        var left = App(Qualified("Fin", "castSucc"), j);
        var right = App(Qualified("Fin", "succ"), j);
        var diagonal = PlusOf(Entry(top, left), Entry(bottom, right));
        var antidiagonal = PlusOf(Entry(top, right), Entry(bottom, left));
        var abs = App(Qualified("Int", "natAbs"), MinusOf(Parenthesized(diagonal), Parenthesized(antidiagonal)));
        var body = All("i", Call("Fin", n), All("j", Call("Fin", k), Eq(abs, D(4))));
        return Dimensions(All("A", Call("Grid", n, k),
            Seq(Parenthesized(Call("Legal", a)), Sp, Iff, Sp, Parenthesized(body))));
    }

    private static Formula CountDefinition()
    {
        var n = V("n");
        var k = V("k");
        var a = V("A");
        var arrays = Seq(OpenBrace, a, Colon, Sp, Call("Grid", n, k), Sp, Mid, Sp,
            Call("Legal", a), CloseBrace);
        var count = Parenthesized(Seq(App(Qualified("Nat", "card"), arrays),
            Colon, Sp, V("Int")));
        return Dimensions(Eq(Call("T", n, k), count));
    }

    private static Formula RecurrenceStatement()
    {
        var d = V("d");
        var n = Seq(d, Dot, D(1));
        var k = Seq(d, Dot, D(2));
        var pair = Seq(V("Nat"), Sp, Times, Sp, V("Nat"));
        var both = Seq(Parenthesized(Recurrence(n, i => Call("T", i, k))), Sp, Land, Sp,
            Parenthesized(Recurrence(k, j => Call("T", n, j))));
        return All("d", pair, ImpliesFrom(Seq(D(0), Sp, Lt, Sp, n),
            ImpliesFrom(Seq(D(0), Sp, Lt, Sp, k), both)));
    }

    private static Formula Recurrence(Formula index, Func<Formula, Formula> count)
    {
        Formula At(byte lag) => count(PlusOf(index, D(lag)));
        var right = PlusOf(TimesOf(D(3), At(5)), TimesOf(D(3), At(4)));
        right = MinusOf(right, TimesOf(D(1, 5), At(3)));
        right = PlusOf(right, TimesOf(D(4), At(2)));
        right = PlusOf(right, TimesOf(D(1, 8), At(1)));
        right = MinusOf(right, TimesOf(D(1, 2), count(index)));
        return Eq(At(6), right);
    }

    private static Formula Dimensions(Formula body) => All("n", V("Nat"), All("k", V("Nat"), body));
    private static Formula V(string name) => F.Id(name);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        App(Seq(Operatorname, Grp(V(name))), args);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula ImpliesFrom(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula PlusOf(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula MinusOf(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula TimesOf(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
}
