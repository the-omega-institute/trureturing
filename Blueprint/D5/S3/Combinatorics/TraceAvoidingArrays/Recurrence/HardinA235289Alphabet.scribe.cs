using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence;

internal sealed class HardinA235289AlphabetDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Alphabet";
    private const string Baseline = "D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.T";
    private const string Note = "D5/L/Automata/hardin2014a235289";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hardin's alphabet comparison for literal constant-stress rectangles.",
        H("Hardin's constant-stress alphabet comparison"),
        Blocks(
            Describe.Lean(DescribeId.Create("literal-count"), DeclarationHandle.Create(Owner + ".literalCount"),
                H("Literal count at alphabet parameter i"),
                StatementSource.FromAuthor(Disp(LiteralCountDefinition())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every indexed filling contributes once. Each pair of indices r and c "
                    + "selects the upper left corner of one contiguous block. Fin.castSucc preserves the index "
                    + "and Fin.succ increments it in the larger axis. The four entries are cast to integers "
                    + "before taking the difference of the diagonal and antidiagonal sums."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Owner + ".result"),
                H("Equality of the four literal counts"),
                StatementSource.FromAuthor(Disp(Comparison())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(
                    Paragraph(Text("The integer count "), Ref(Baseline),
                        Text(" uses the alphabet 0 through 3 and absolute diagonal difference four. "
                            + "Each filling of the indexed rectangle contributes once. The four choices of i give "
                            + "alphabet maxima 3, 4, 5, 6 and absolute differences 4, 6, 8, 10.")),
                    Paragraph(Text("Write M = i+2 for the alphabet maximum. Replacing each entry x on one "
                        + "checkerboard color by M−x converts the block condition into a choice of sums "
                        + "2 and 4M−2. Adjacent blocks share two cells, so their sums differ by at most 2M. "
                        + "For M at least 3 the two allowed sums differ by more than 2M. Every block sum "
                        + "therefore agrees with the sum in the corner block.")),
                    Paragraph(Text("Complementing all entries exchanges the two classes. Every cell of a positive "
                        + "rectangle belongs to a block, so in the sum-two class every entry is 0, 1, or 2. "
                        + "Restricting the alphabet to these three entries and embedding it back are inverse. "
                        + "The count at each specified alphabet is twice the cardinality of this same class. "
                        + "The four-symbol baseline has that same count by its checkerboard and complement identity."))),
                DescribeRole.Theorem))));

    private static Formula LiteralCountDefinition()
    {
        var n = V("n");
        var k = V("k");
        var i = V("i");
        var a = V("A");
        var r = V("r");
        var c = V("c");
        var grid = Seq(Call("Fin", Add(n, D(1))), Sp, To, Sp,
            Call("Fin", Add(k, D(1))), Sp, To, Sp, Call("Fin", Add(i, D(3))));
        Formula Entry(string row, string column) => Parenthesized(Seq(
            Call("val", App(a, App(Qualified("Fin", row), r), App(Qualified("Fin", column), c))),
            Colon, Sp, V("Int")));
        var diagonal = Add(Entry("castSucc", "castSucc"), Entry("succ", "succ"));
        var antidiagonal = Add(Entry("castSucc", "succ"), Entry("succ", "castSucc"));
        var absoluteDifference = App(Qualified("Int", "natAbs"),
            new Formula.Binary(Parenthesized(diagonal), FormulaBinaryOperator.Subtract,
                Parenthesized(antidiagonal)));
        var stress = Add(D(2), new Formula.Binary(D(2), FormulaBinaryOperator.Multiply, i));
        var constraint = All("r", Call("Fin", n), All("c", Call("Fin", k), Equal(absoluteDifference, stress)));
        var arrays = Seq(OpenBrace, a, Colon, Sp, grid, Sp, Mid, Sp, constraint, CloseBrace);
        var count = Parenthesized(Seq(App(Qualified("Nat", "card"), arrays), Colon, Sp, V("Int")));
        return ForDimensions(Equal(Call("literalCount", n, k, i), count));
    }

    private static Formula Comparison()
    {
        var n = V("n");
        var k = V("k");
        var i = V("i");
        var choices = Seq(Equal(i, D(1)), Sp, Lor, Sp, Equal(i, D(2)), Sp, Lor, Sp,
            Equal(i, D(3)), Sp, Lor, Sp, Equal(i, D(4)));
        return ForDimensions(
            ImpliesFrom(Seq(D(1), Sp, Le, Sp, n), ImpliesFrom(Seq(D(1), Sp, Le, Sp, k),
                ImpliesFrom(choices, Equal(Call("literalCount", n, k, i), Call("T", n, k))))));
    }

    private static Formula ForDimensions(Formula body) =>
        All("n", V("Nat"), All("k", V("Nat"), All("i", V("Nat"), body)));

    private static Formula V(string name) => F.Id(name);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        App(Seq(Operatorname, Grp(V(name))), args);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, F.Eq, Sp, right);
    private static Formula ImpliesFrom(Formula hypothesis, Formula conclusion) =>
        Seq(Parenthesized(hypothesis), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
}
