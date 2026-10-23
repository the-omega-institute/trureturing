using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.BlockPalindromes;

internal sealed class CompositionInversionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/BlockPalindromes/CompositionInversion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/gabricshallit2023blockpalindromes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stable A274190 diagonals and inversion of the unbordered-word series.",
        H("CompositionInversion"), Blocks(
            Node("bpal-a274190", "a274190",
                Disp(Seq(Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("n"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Const("a274190"), Sp, FormulaDsl.Id("n"), Sp, D(0), Sp, Eq, Sp, D(1))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("m"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Const("a274190"), Sp, D(0), Sp, Parenthesized(Seq(FormulaDsl.Id("m"), Sp, Plus, Sp, D(1))), Sp, Eq, Sp, D(0))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("n"), Sp, FormulaDsl.Id("m"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Const("a274190"), Sp, Parenthesized(Seq(FormulaDsl.Id("n"), Sp, Plus, Sp, D(1))), Sp, Parenthesized(Seq(FormulaDsl.Id("m"), Sp, Plus, Sp, D(1))), Sp, Eq, Sp, Const("if"), Sp, FormulaDsl.Id("m"), Sp, Plus, Sp, D(1), Sp, Leq, Sp, FormulaDsl.Id("n"), Sp, Plus, Sp, D(1), Sp, Const("then"), Sp, Const("a274190"), Sp, FormulaDsl.Id("n"), Sp, FormulaDsl.Id("m"), Sp, Plus, Sp, Const("a274190"), Sp, FormulaDsl.Id("n"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Parenthesized(Seq(FormulaDsl.Id("m"), Sp, Plus, Sp, D(1))))), Sp, Const("else"), Sp, D(0))))),
                "The recurrence is the A274190 triangle, with row zero and column zero included. Its reverse diagonal stabilizes to A274199.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bpal-a274190-stable", "a274190_stable",
                Disp(Seq(Forall, Sp, FormulaDsl.Id("N"), Sp, FormulaDsl.Id("d"), Sp, Colon, Sp, N(), Sp, Comma, Sp, D(2), Sp, Cdot, Sp, FormulaDsl.Id("d"), Sp, Leq, Sp, FormulaDsl.Id("N"), Sp, Rightarrow, Sp, Const("a274190"), Sp, FormulaDsl.Id("N"), Sp, Parenthesized(Seq(FormulaDsl.Id("N"), Sp, Minus, Sp, FormulaDsl.Id("d"))), Sp, Eq, Sp, Const("a274190"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, FormulaDsl.Id("d"))), Sp, FormulaDsl.Id("d"))),
                "The displayed statement holds for all of its quantified arguments.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("bpal-a274190-diagonal-limit", "a274190_diagonal_limit",
                Disp(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("d"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Const("Tendsto"), Sp, Parenthesized(Seq(Const("fun"), Sp, FormulaDsl.Id("N"), Sp, Colon, Sp, N(), Sp, Mapsto, Sp, Parenthesized(Seq(Const("a274190"), Sp, FormulaDsl.Id("N"), Sp, Parenthesized(Seq(FormulaDsl.Id("N"), Sp, Minus, Sp, FormulaDsl.Id("d"))), Sp, Colon, Sp, R())))), Sp, Const("atTop"), Sp, Parenthesized(Seq(Const("nhds"), Sp, Parenthesized(Seq(Const("a274190"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, FormulaDsl.Id("d"))), Sp, FormulaDsl.Id("d"), Sp, Colon, Sp, R())))))),
                "The displayed statement holds for all of its quantified arguments.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("bpal-compcount", "compCount",
                Disp(Seq(Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("b"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Const("compCount"), Sp, D(0), Sp, FormulaDsl.Id("b"), Sp, Eq, Sp, D(1))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("n"), Sp, FormulaDsl.Id("b"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Const("compCount"), Sp, Parenthesized(Seq(FormulaDsl.Id("n"), Sp, Plus, Sp, D(1))), Sp, FormulaDsl.Id("b"), Sp, Eq, Sp, Seq(Sum, Underscore, Grp(Seq(FormulaDsl.Id("i"), Sp, InMacro, Sp, Const("Finset"), Sp, Dot, Sp, Const("range"), Sp, Parenthesized(Seq(FormulaDsl.Id("n"), Sp, Plus, Sp, D(1)))))), Sp, Const("if"), Sp, FormulaDsl.Id("i"), Sp, Plus, Sp, D(1), Sp, Leq, Sp, FormulaDsl.Id("b"), Sp, Const("then"), Sp, Const("compCount"), Sp, Parenthesized(Seq(FormulaDsl.Id("n"), Sp, Minus, Sp, FormulaDsl.Id("i"))), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, FormulaDsl.Id("i"), Sp, Plus, Sp, D(1))), Sp, Const("else"), Sp, D(0))))),
                "The defining expression of compCount.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("bpal-a274190-compcount", "a274190_compCount",
                Disp(Seq(Forall, Sp, FormulaDsl.Id("N"), Sp, FormulaDsl.Id("m"), Sp, Colon, Sp, N(), Sp, Comma, Sp, FormulaDsl.Id("m"), Sp, Leq, Sp, FormulaDsl.Id("N"), Sp, Rightarrow, Sp, Const("a274190"), Sp, FormulaDsl.Id("N"), Sp, FormulaDsl.Id("m"), Sp, Eq, Sp, Const("compCount"), Sp, Parenthesized(Seq(FormulaDsl.Id("N"), Sp, Minus, Sp, FormulaDsl.Id("m"))), Sp, Parenthesized(Seq(FormulaDsl.Id("m"), Sp, Plus, Sp, D(1))))),
                "The recurrence of the reverse triangle is the first-part recurrence for compositions whose next part is less than twice its predecessor.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("bpal-a274190-stable-compcount", "a274190_stable_compCount",
                Disp(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("d"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Const("a274190"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, FormulaDsl.Id("d"))), Sp, FormulaDsl.Id("d"), Sp, Eq, Sp, Const("compCount"), Sp, FormulaDsl.Id("d"), Sp, FormulaDsl.Id("d"))),
                "The displayed statement holds for all of its quantified arguments.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("bpal-compcount-fib-bound", "compCount_fib_bound",
                Disp(Seq(Forall, Sp, FormulaDsl.Id("n"), Sp, FormulaDsl.Id("b"), Sp, Colon, Sp, N(), Sp, Comma, Sp, Const("compCount"), Sp, FormulaDsl.Id("n"), Sp, FormulaDsl.Id("b"), Sp, Leq, Sp, Const("Nat"), Sp, Dot, Sp, Const("fib"), Sp, Parenthesized(Seq(FormulaDsl.Id("n"), Sp, Plus, Sp, D(1))))),
                "The restricted composition count is at most Nat.fib(n+1). The bound gives absolute convergence at every reciprocal integer alphabet size k≥2.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("bpal-composition-series-summable", "composition_series_summable",
                Disp(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("k"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Parenthesized(Seq(D(2), Sp, Leq, Sp, FormulaDsl.Id("k"))), Sp, Rightarrow, Sp, Parenthesized(Seq(Const("Summable"), Sp, Parenthesized(Seq(Const("fun"), Sp, FormulaDsl.Id("d"), Sp, Colon, Sp, N(), Sp, Mapsto, Sp, Parenthesized(Seq(Const("compCount"), Sp, FormulaDsl.Id("d"), Sp, FormulaDsl.Id("d"), Sp, Colon, Sp, R())), Sp, Slash, Sp, Parenthesized(Seq(FormulaDsl.Id("k"), Sp, Colon, Sp, R())), Sp, Seq(Caret, Grp(FormulaDsl.Id("d"))))))))),
                "The displayed statement holds for all of its quantified arguments.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("bpal-compterm", "compTerm",
                Disp(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("k"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("b"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("d"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Const("compTerm"), Sp, FormulaDsl.Id("k"), Sp, FormulaDsl.Id("b"), Sp, FormulaDsl.Id("d"), Sp, Eq, Sp, Parenthesized(Seq(Const("compCount"), Sp, FormulaDsl.Id("d"), Sp, FormulaDsl.Id("b"), Sp, Colon, Sp, R())), Sp, Slash, Sp, Parenthesized(Seq(FormulaDsl.Id("k"), Sp, Colon, Sp, R())), Sp, Seq(Caret, Grp(FormulaDsl.Id("d"))))),
                "The defining expression of compTerm.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("bpal-totalseries", "totalSeries",
                Disp(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("k"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Const("totalSeries"), Sp, FormulaDsl.Id("k"), Sp, Eq, Sp, Seq(Sum, Apos, Underscore, Grp(Seq(FormulaDsl.Id("d"), Sp, Colon, Sp, N()))), Sp, Const("compTerm"), Sp, FormulaDsl.Id("k"), Sp, FormulaDsl.Id("d"), Sp, FormulaDsl.Id("d"))),
                "The defining expression of totalSeries.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("bpal-unbordered-composition-series", "unbordered_composition_series",
                Disp(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("k"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Parenthesized(Seq(D(2), Sp, Leq, Sp, FormulaDsl.Id("k"))), Sp, Rightarrow, Sp, Parenthesized(Seq(Const("totalSeries"), Sp, FormulaDsl.Id("k"), Sp, Eq, Sp, D(1), Sp, Slash, Sp, Parenthesized(Seq(D(1), Sp, Minus, Sp, FormulaDsl.Id("q"), Sp, FormulaDsl.Id("k"), Sp, Parenthesized(Seq(Const("uCount"), Sp, FormulaDsl.Id("k"))))))))),
                "Pairing the two regions j<2i and 2i≤j cancels their signed convolution contributions. The remaining identity relates the unbordered-word series to the full restricted-composition series.", DescribeRole.Theorem, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string id, string name, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(name),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Const(string name) => Seq(Operatorname, Grp(FormulaDsl.Id(name)));
    private static Formula N() => Seq(Mathbb, Grp(FormulaDsl.Id("N")));
    private static Formula R() => Seq(Mathbb, Grp(FormulaDsl.Id("R")));
}
