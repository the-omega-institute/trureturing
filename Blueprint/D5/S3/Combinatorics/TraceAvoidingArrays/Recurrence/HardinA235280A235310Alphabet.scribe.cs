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
            Describe.Lean(DescribeId.Create("indexed-grid"), DeclarationHandle.Create(Owner + ".Grid"),
                H("Indexed grids"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Grid(M,n,k) consists of functions from Fin (n+1) × Fin (k+1) "
                    + "to Fin (M+1)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("block-sum"), DeclarationHandle.Create(Owner + ".block"),
                H("Contiguous block sum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The block at (r,c) sums the entries in rows r and r+1 "
                    + "and columns c and c+1."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sum-d-grid"), DeclarationHandle.Create(Owner + ".Low"),
                H("Grids of block sum d"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Low(d,a) requires the natural sum of the four entries "
                    + "in every contiguous block of a to equal d."))),
                DescribeRole.Definition),
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
            Describe.Lean(DescribeId.Create("fixed-deficit-equiv"),
                DeclarationHandle.Create(Owner + ".fixedDeficitEquiv"),
                H("Fixed-deficit equivalence"), StatementSource.FromAuthor(Disp(FixedDeficitStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The successor indices n+1 and k+1 give n+2 rows and k+2 columns. "
                    + "Legal(S,a) is the absolute diagonal difference condition in every "
                    + "contiguous block. Sum denotes the tagged disjoint union.")),
                    Paragraph(Text("Checkerboard complementation gives block sums d and 4M−d. "
                    + "The gap exceeds the change possible across a shared edge, so the sum is uniform. "
                    + "The first copy comes from the low class. Global complementation sends the high "
                    + "class to the low class for the second copy. Every entry in a low-class grid "
                    + "is at most d, so both copies use the alphabet 0 through d."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fixed-deficit-count"), DeclarationHandle.Create(Owner + ".count_eq"),
                H("Count at fixed deficit"), StatementSource.FromAuthor(Disp(FixedDeficitCountStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive n and k, the two block-sum classes give equal "
                    + "contributions after restriction to the alphabet 0 through d."))),
                DescribeRole.Theorem),
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

    private static Formula FixedDeficitStatement()
    {
        var m = V("M");
        var d = V("d");
        var n = Add(V("n"), D(1));
        var k = Add(V("k"), D(1));
        var a = V("a");
        Formula Subtype(Formula maximum, Formula condition) =>
            Seq(OpenBrace, a, Colon, Sp, Call("Grid", maximum, n, k), Sp, Mid, Sp, condition, CloseBrace);
        var stress = new Formula.Binary(new Formula.Binary(D(2), FormulaBinaryOperator.Multiply, m),
            FormulaBinaryOperator.Subtract, d);
        var legal = Subtype(m, Call("Legal", stress, a));
        var low = Subtype(d, Call("Low", d, a));
        var codomain = Call("Sum", low, low);
        return All("M", V("Nat"), All("d", V("Nat"), ForDimensions(
            ImpliesFrom(Seq(d, Sp, Lt, Sp, m), Seq(legal, Sp, Equiv, Sp, codomain)))));
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

    private static Formula FixedDeficitCountStatement()
    {
        var m = V("M");
        var d = V("d");
        var n = V("n");
        var k = V("k");
        var a = V("a");
        var stress = new Formula.Binary(new Formula.Binary(D(2), FormulaBinaryOperator.Multiply, m),
            FormulaBinaryOperator.Subtract, d);
        var low = Seq(OpenBrace, a, Colon, Sp, Call("Grid", d, n, k), Sp, Mid, Sp, Call("Low", d, a), CloseBrace);
        var twice = new Formula.Binary(D(2), FormulaBinaryOperator.Multiply, App(Qualified("Nat", "card"), low));
        return All("M", V("Nat"), All("d", V("Nat"), ForDimensions(
            ImpliesFrom(Seq(d, Sp, Lt, Sp, m),
                ImpliesFrom(Seq(D(1), Sp, Le, Sp, n),
                    ImpliesFrom(Seq(D(1), Sp, Le, Sp, k), Equal(Call("C", m, stress, n, k), twice)))))));
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
