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
                    Paragraph(Text("For a sum-two array, the horizontal adjacent sums in successive rows alternate between a profile and its complement in two. If the first edge sum is s, the initial entry can range from 0 to s, giving at most s+1 choices. The complement has first edge sum 2−s, giving at most 3−s initial choices. The initial entry determines the row from its adjacent sums, so the profile and its complement have at most four row choices in total. The nonzero contributions have one-step multiplier one or two, or two-step multiplier two or three. Each contribution satisfies the displayed recurrence, and summing the contributions proves the first identity. Transposition gives the second."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin-a235289-common-recurrence"),
                    ResolutionKind.Proved)),
            PublicSurface("fin-constant", "fin_constant", "Adjacent equality on a finite interval",
                FinConstantStatement(),
                "If a function agrees at each adjacent pair, its value at every index is its value at zero.",
                DescribeRole.Lemma),
            PublicSurface("profile", "Profile", "Row profiles", ProfileDefinition(),
                "A profile assigns one of 0, 1 or 2 to each of the k horizontal edges of a row with k+1 cells.",
                DescribeRole.Definition),
            PublicSurface("edge", "edge", "Adjacent entry sum", EdgeDefinition(),
                "Every row uses the alphabet 0 through 3. The sum at an edge is a natural number and can be as large as six.",
                DescribeRole.Definition),
            PublicSurface("fiber", "Fiber", "Rows realizing a profile", FiberDefinition(),
                "The subtype fixes the natural sum at every edge to the corresponding profile entry.",
                DescribeRole.Definition),
            PublicSurface("flip", "flip", "Complementary profiles", FlipDefinition(),
                "Reversal in Fin 3 sends each profile value s to 2−s at the same edge.",
                DescribeRole.Definition),
            PublicSurface("b", "b", "Row multiplicity", MultiplicityDefinition(),
                "The natural cardinality of the fiber counts individual rows with the prescribed edge sums.",
                DescribeRole.Definition),
            PublicSurface("profile-count", "profileCount", "Alternating row-profile count",
                ProfileCountDefinition(),
                "At an even row index choose the profile p, and at an odd index choose its complement. "
                + "The three arguments of if give the condition, the even choice and the odd choice. "
                + "The finite product is a natural number and the empty product is one.",
                DescribeRole.Definition),
            PublicSurface("profile-count-two-step", "profileCount_two_step", "Adding two rows",
                ProfileCountTwoStepStatement(),
                "Adding two rows multiplies the natural count by the two complementary fiber sizes.",
                DescribeRole.Lemma),
            PublicSurface("profile-count-eq-pow", "profileCount_eq_pow", "Equal row multiplicities",
                ProfileCountPowerStatement(),
                "If both complementary fibers have the same size c, every row gives c choices.",
                DescribeRole.Lemma),
            PublicSurface("literal-sum", "literal_sum", "Profile sum for the rectangular count",
                LiteralSumStatement(),
                "There are n+2 rows and k+2 columns here. The two uniform block-sum classes give the factor of two. "
                + "Each natural alternating row-profile count is cast to an integer before the sum.",
                DescribeRole.Lemma),
            PublicSurface("t-transpose", "T_transpose", "Transposition of the literal count",
                TransposeStatement(),
                "Transposition swaps the grid dimensions and preserves the contiguous block condition. "
                + "The count identity holds at all natural indices.",
                DescribeRole.Lemma))));

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
        return Dimensions(Eq(Call("Grid", n, k), Parenthesized(grid)));
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

    private static DocumentBlock PublicSurface(
        string id, string name, string title, Formula formula, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    private static Formula FinConstantStatement()
    {
        var n = V("n");
        var i = V("i");
        var j = V("j");
        var f = V("f");
        Formula At(string embedding) => App(f, App(Qualified("Fin", embedding), j));
        var domain = Call("Fin", PlusOf(n, D(1)));
        var adjacent = All("j", Call("Fin", n), Eq(At("castSucc"), At("succ")));
        var conclusion = All("i", domain, Eq(App(f, i), App(f, D(0))));
        return All("n", V("Nat"), All("A", V("Type"),
            All("f", Arrow(domain, V("A")), ImpliesFrom(adjacent, conclusion))));
    }

    private static Formula ProfileDefinition()
    {
        var k = V("k");
        return All("k", V("Nat"), Eq(Call("Profile", k),
            Parenthesized(Arrow(Call("Fin", k), Call("Fin", D(3))))));
    }

    private static Formula EdgeDefinition()
    {
        var k = V("k");
        var r = V("r");
        var j = V("j");
        Formula Entry(string embedding) => Call("val", App(r, App(Qualified("Fin", embedding), j)));
        return All("k", V("Nat"), All("r", RowType(k), All("j", Call("Fin", k),
            Eq(Call("edge", r, j), PlusOf(Entry("castSucc"), Entry("succ"))))));
    }

    private static Formula FiberDefinition()
    {
        var k = V("k");
        var p = V("p");
        var r = V("r");
        var j = V("j");
        var realizes = All("j", Call("Fin", k), Eq(Call("edge", r, j), Call("val", App(p, j))));
        var rows = Seq(OpenBrace, r, Colon, Sp, Parenthesized(RowType(k)), Sp, Mid, Sp,
            realizes, CloseBrace);
        return ForProfile(k, Eq(Call("Fiber", p), rows));
    }

    private static Formula FlipDefinition()
    {
        var k = V("k");
        var p = V("p");
        var j = V("j");
        return ForProfile(k, All("j", Call("Fin", k),
            Eq(App(Call("flip", p), j), App(Qualified("Fin", "rev"), App(p, j)))));
    }

    private static Formula MultiplicityDefinition()
    {
        var k = V("k");
        var p = V("p");
        return ForProfile(k, Eq(Call("b", p), App(Qualified("Nat", "card"), Call("Fiber", p))));
    }

    private static Formula ProfileCountDefinition()
    {
        var k = V("k");
        var p = V("p");
        var h = V("h");
        var even = Eq(new Formula.Modulo(Call("val", V("i")), D(2)), D(0));
        var choice = Call("if", Parenthesized(even), p, Call("flip", p));
        var product = Over(Prod, "i", Call("Fin", h), Call("b", choice));
        return ForProfileHeight(k, Eq(Call("profileCount", p, h), product));
    }

    private static Formula ProfileCountTwoStepStatement()
    {
        var k = V("k");
        var p = V("p");
        var h = V("h");
        var pair = TimesOf(Call("b", p), Call("b", Call("flip", p)));
        return ForProfileHeight(k, Eq(Call("profileCount", p, PlusOf(h, D(2))),
            TimesOf(pair, Call("profileCount", p, h))));
    }

    private static Formula ProfileCountPowerStatement()
    {
        var k = V("k");
        var p = V("p");
        var h = V("h");
        var c = V("c");
        return ForProfile(k, All("c", V("Nat"),
            ImpliesFrom(Eq(Call("b", p), c), ImpliesFrom(Eq(Call("b", Call("flip", p)), c),
                All("h", V("Nat"), Eq(Call("profileCount", p, h), new Formula.Power(c, h)))))));
    }

    private static Formula LiteralSumStatement()
    {
        var n = V("n");
        var k = V("k");
        var p = V("p");
        var profiles = Call("Profile", PlusOf(k, D(1)));
        var count = Parenthesized(Seq(Call("profileCount", p, PlusOf(n, D(2))), Colon, Sp, V("Int")));
        var sum = Over(Sum, "p", profiles, TimesOf(D(2), count));
        return Dimensions(Eq(Call("T", PlusOf(n, D(1)), PlusOf(k, D(1))), sum));
    }

    private static Formula TransposeStatement()
    {
        var n = V("n");
        var k = V("k");
        return Dimensions(Eq(Call("T", n, k), Call("T", k, n)));
    }

    private static Formula RowType(Formula k) =>
        Arrow(Call("Fin", PlusOf(k, D(1))), Call("Fin", D(4)));

    private static Formula Arrow(Formula from, Formula to) => new Formula.TypeArrow(from, to);

    private static Formula ForProfile(Formula k, Formula body) =>
        All("k", V("Nat"), All("p", Call("Profile", k), body));

    private static Formula ForProfileHeight(Formula k, Formula body) =>
        ForProfile(k, All("h", V("Nat"), body));

    private static Formula Over(Formula op, string variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(op, Seq(V(variable), Colon, Sp, type)), Sp, Parenthesized(body));

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
