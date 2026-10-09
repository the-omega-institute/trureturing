using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class PaddedWordPartitionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/PaddedWordPartition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reverse list of horizontal prefix counts at vertical letters is a padded decreasing partition. Its row and conjugate column squares determine the two centered moments of the same word at its direct area count.",
        H("Direct prefix partitions and their two fan moments"),
        Blocks(
            Node("prefix-rows", "Zero-padded reverse prefix rows", "rows", DescribeRole.Definition, RowsFormula(),
                "At every false letter, record the number of preceding true letters, then reverse the recorded list. The list contains one entry for every false letter, including zero entries. Its sum is the scattered true-before-false count and each row is bounded by the total true count."),
            Node("actual-diagram", "The actual Young diagram", "diagram", DescribeRole.Definition, DiagramFormula(),
                "The decreasing padded list defines a Young diagram by its cells; rowsSorted(w) denotes its decreasing-order proof rows_sorted w. Zero entries stay in the padded list even though they contribute no cells. The row statistic is the sum of the row squares. The column statistic sums the squares of the rows of this very diagram's transpose, padded to the true count."),
            Node("row-squares", "Squares of the padded rows", "P", DescribeRole.Definition, RowSquaresFormula(),
                "The index ranges over every entry of the padded row list. The natural row length is cast to the reals before squaring."),
            Node("column-squares", "Squares of the actual transpose rows", "R", DescribeRole.Definition, ColumnSquaresFormula(),
                "The natural column length is the row length of the same diagram's transpose. The sum ranges from zero to the true count minus one, including zero columns."),
            Node("same-columns", "Column squares from the same cells", "same_diagram_columns", DescribeRole.Theorem, ColumnsFormula(),
                "A column of height h has square equal to the sum of the first h odd positive integers. Summing over columns and interchanging the finite cell sums gives the odd-position weighted sum of the original rows. The equality uses membership in one diagram and its actual transpose."),
            Node("direct-fan", "All words at direct area", "all_word_direct", DescribeRole.Theorem, DirectFormula(),
                "For every binary word, with u true letters, v false letters, K scattered true-before-false pairs, row-square sum P and transposed column-square sum R, the exact coordinates are D = 2K - uv, E = u squared times v - 6uK + 6P, and F = minus u times v squared + 6vK - 6R. K is used directly, including values above half the rectangle area. Empty auxiliary words, pure-letter words and zero signed area need no additional hypothesis or division. Actual acquisition, common calibration and exact arithmetic remain independent premises when the formula is used for a physical source.")),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, Seq(Open, right, Close));
    private static Formula WordType() => Call("List", F.Id("Bool"));
    private static Formula Count(Formula w, string letter) => Call("count", w, F.Id(letter));
    private static Formula Real(Formula n) => Call("real", n);
    private static Formula Square(Formula n) => new Formula.Power(n, D(2));

    private static Formula RowsFormula()
    {
        Formula w = F.Id("w"), x = F.Id("x"), empty = Seq(OpenBracket, CloseBracket);
        Formula successor = Seq(Open, x, Colon, F.Id("Nat"), Mapsto, Sp, x, Plus, D(1), Close);
        return Disp(All("w", WordType(), And(Equal(Call("rows", empty), empty), And(
            Equal(Call("rows", Call("cons", F.Id("true"), w)),
                Call("map", successor, Call("rows", w))),
            Equal(Call("rows", Call("cons", F.Id("false"), w)),
                Call("append", Call("rows", w), Seq(OpenBracket, D(0), CloseBracket)))))));
    }

    private static Formula DiagramFormula()
    {
        Formula w = F.Id("w");
        return Disp(All("w", WordType(), Equal(Call("diagram", w),
            Call("ofRowLens", Call("rows", w), Call("rowsSorted", w)))));
    }

    private static Formula RowSquaresFormula()
    {
        Formula w = F.Id("w"), i = F.Id("i");
        Formula sum = Seq(Sum, Underscore, Grp(i, Colon,
            Call("Fin", Call("length", Call("rows", w)))), Sp,
            Square(Real(Call("rowLen", Call("diagram", w), i))));
        return Disp(All("w", WordType(), Equal(Call("P", w), sum)));
    }

    private static Formula ColumnSquaresFormula()
    {
        Formula w = F.Id("w"), j = F.Id("j");
        Formula sum = Seq(Sum, Underscore, Grp(j, InMacro, Sp,
            Call("range", Count(w, "true"))), Sp,
            Square(Real(Call("rowLen", Call("transpose", Call("diagram", w)), j))));
        return Disp(All("w", WordType(), Equal(Call("R", w), sum)));
    }

    private static Formula ColumnsFormula()
    {
        Formula w = F.Id("w");
        return Disp(All("w", WordType(), Equal(Call("R", w), Call("oddRows", Call("rows", w)))));
    }

    private static Formula DirectFormula()
    {
        Formula w = F.Id("w"), u = Real(Count(w, "true")), v = Real(Count(w, "false")),
            k = Real(Call("scatteredTrueFalseCount", w));
        return Disp(All("w", WordType(), Equal(Call("G", w), Call("Five", u, v,
            Seq(D(2), k, Minus, u, v),
            Seq(Square(u), v, Minus, D(6), u, k, Plus, D(6), Call("P", w)),
            Seq(Minus, u, Square(v), Plus, D(6), v, k, Minus, D(6), Call("R", w))))));
    }
}
