using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence;

internal sealed class HardinA235280A235310AlphabetDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hardin's literal constant-stress alphabet comparisons for A235280 and A235310.",
        H("Hardin's constant-stress alphabet comparisons"),
        Blocks(
            new DocumentBlock.Section(H("Source GID"), Blocks(Paragraph(Ref(Owner)))),
            Describe.Lean(DescribeId.Create("literal-count"), DeclarationHandle.Create(Owner + ".C"),
                H("Literal indexed count"), StatementSource.FromAuthor(Disp(LiteralCountDefinition())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coordinates are ordered. Each legal filling contributes once. "
                    + "The contiguous block condition tests the absolute difference of the two integer sums."))),
                DescribeRole.Definition),
            Paragraph(Text("For positive n and k, a fixed deficit d, and M greater than d, "
                + "checkerboard complementation sends stress 2M−d to block sums d and 4M−d. The gap is greater than the change possible "
                + "across a shared edge, so the sum is uniform. Global complementation pairs the two "
                + "classes. Every entry in the low class is at most d, and restricting the alphabet "
                + "gives the exact count as twice the cardinality of the sum-d class over Fin (d+1).")),
            Endpoint("a235280", "A235280", "hardin2014a235280", "hardin-a235280-alphabet-comparison",
                Comparison((4, 5), (5, 7), (6, 9)), "The common deficit is three. The NAME count is C(4, 5, n, k)."),
            Endpoint("a235310", "A235310", "hardin2014a235310", "hardin-a235310-alphabet-comparison",
                Comparison((5, 6), (6, 8), (7, 10)), "The common deficit is four. The NAME count is C(5, 6, n, k)."))));

    private static DocumentBlock Endpoint(string name, string sequence, string bibkey, string slug,
        Formula statement, string correspondence) =>
        Describe.Lean(DescribeId.Create(name), DeclarationHandle.Create(Owner + "." + name),
            H(sequence + " alphabet comparison"), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Automata/" + bibkey)),
            Blocks(Paragraph(Text(correspondence + " The COMMENT specifies i = 1, 2, 3."))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create(slug), ResolutionKind.Proved));

    private static Formula LiteralCountDefinition()
    {
        var m = V("M");
        var s = V("S");
        var n = V("n");
        var k = V("k");
        var a = V("a");
        var r = V("r");
        var c = V("c");
        var coordinates = Seq(Call("Fin", Add(n, D(1))), Sp, Times, Sp, Call("Fin", Add(k, D(1))));
        var grid = Seq(Parenthesized(coordinates), Sp, To, Sp, Call("Fin", Add(m, D(1))));
        Formula Entry(string row, string column)
        {
            var point = Parenthesized(Seq(App(Qualified("Fin", row), r), Comma, Sp,
                App(Qualified("Fin", column), c)));
            return Parenthesized(Seq(Call("val", App(a, point)), Colon, Sp, V("Int")));
        }

        var diagonal = Add(Entry("castSucc", "castSucc"), Entry("succ", "succ"));
        var antidiagonal = Add(Entry("castSucc", "succ"), Entry("succ", "castSucc"));
        var difference = App(Qualified("Int", "natAbs"), new Formula.Binary(
            Parenthesized(diagonal), FormulaBinaryOperator.Subtract, Parenthesized(antidiagonal)));
        var legal = All("r", Call("Fin", n), All("c", Call("Fin", k), Equal(difference, s)));
        var arrays = Seq(OpenBrace, a, Colon, Sp, grid, Sp, Mid, Sp, legal, CloseBrace);
        return All("M", V("Nat"), All("S", V("Nat"), ForDimensions(
            Equal(Call("C", m, s, n, k), App(Qualified("Nat", "card"), arrays)))));
    }

    private static Formula Comparison((byte Max, byte Stress) first, (byte Max, byte Stress) second,
        (byte Max, byte Stress) third)
    {
        var n = V("n");
        var k = V("k");
        Formula Count((byte Max, byte Stress) pair) => Call("C", Num(pair.Max), Num(pair.Stress), n, k);
        var equalities = Seq(Parenthesized(Equal(Count(first), Count(second))), Sp, Land, Sp,
            Parenthesized(Equal(Count(second), Count(third))));
        return ForDimensions(ImpliesFrom(Seq(D(1), Sp, Le, Sp, n),
            ImpliesFrom(Seq(D(1), Sp, Le, Sp, k), equalities)));
    }

    private static Formula ForDimensions(Formula body) => All("n", V("Nat"), All("k", V("Nat"), body));

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
