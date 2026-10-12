using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class PaddedWordPartitionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/PaddedWordPartition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A binary word traces positive unit steps in one oriented plane. Signed triangle sums give area and centered first moments, including paths of zero signed area. The reverse list of horizontal prefix counts at vertical letters is a padded decreasing partition. Its row and conjugate column squares determine the two centered moments of the same word at its direct area count.",
        H("Direct prefix partitions and their two fan moments"),
        Blocks(
            Node("actual-fan", "One ordered path", "G", DescribeRole.Definition, FanFormula(),
                "True is the horizontal unit step and false is the vertical unit step. Prefix sums are the vertices of the path. Each consecutive pair contributes its determinant divided by two and that signed area times the sum of its vertices divided by three. The centered vector is the raw moment minus half the area times the endpoint. The five coordinates are the endpoint, twice the signed area, and twelve times each centered moment. No division by the total area occurs."),
            Node("online-rule", "The update using old coordinates", "U", DescribeRole.Definition, UpdateFormula(),
                "All coordinates on the right are from the same old Five value. The true branch adds the horizontal unit step; the false branch adds the vertical unit step."),
            Node("concat-rule", "The common seam correction", "star", DescribeRole.Definition, StarFormula(),
                "The seam determinant is x.u times y.v minus x.v times y.u. The area and both moment corrections use this same determinant and the signed areas of the same two paths."),
            Node("online-fan", "Appending a supplied letter", "G_append", DescribeRole.Theorem, AppendFormula(),
                "Appending a letter preserves the old vertices and adds their last triangle. The resulting arithmetic uses the old endpoint and old signed area. It is valid for the empty auxiliary word as well as every nonempty word."),
            Node("concat-fan", "Concatenating two paths", "G_concat", DescribeRole.Theorem, ConcatFormula(),
                "The five coordinates of a concatenation satisfy the signed fan concatenation formula. Both moment coordinates include the endpoint and signed-area seam terms of the same two paths."),
            Node("reverse-fan", "Reversing the complete word", "G_reverse", DescribeRole.Theorem, ReverseFormula(),
                "Reversal fixes both letter counts, negates signed area, and preserves both centered moment coordinates. This statement compares mathematical positive words in a common unit reference. It supplies no operation, acquisition, calibration, or reversal authority over a physical source."),
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
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Field(Formula x, string name) => Seq(x, Dot, F.Id(name));
    private static Formula Tuple(params Formula[] coordinates) => Call("Five", coordinates);
    private static Formula Append(Formula x, Formula y) => Call("append", x, y);

    private static Formula FanFormula()
    {
        Formula w = F.Id("w"), q = Call("q", w), m = Call("m", w);
        return Disp(All("w", WordType(), Equal(Call("G", w), Tuple(
            Seq(q, Dot, D(1)), Seq(q, Dot, D(2)), Seq(D(2), Call("A", w)),
            Seq(D(1, 2), m, Dot, D(1)), Seq(D(1, 2), m, Dot, D(2))))));
    }

    private static Formula UpdateFormula()
    {
        Formula x = F.Id("x"), c = F.Id("c"), u = Field(x, "u"), v = Field(x, "v"),
            d = Field(x, "d"), e = Field(x, "e"), f = Field(x, "f");
        Formula horizontal = Tuple(Seq(u, Plus, D(1)), v, Seq(d, Minus, v),
            Seq(e, Minus, D(3), d, Minus, Multiply(u, v), Plus, v),
            Seq(f, Minus, new Formula.Power(v, D(2))));
        Formula vertical = Tuple(u, Seq(v, Plus, D(1)), Seq(d, Plus, u),
            Seq(e, Plus, new Formula.Power(u, D(2))),
            Seq(f, Minus, D(3), d, Plus, Multiply(u, v), Minus, u));
        return Disp(All("x", F.Id("Five"), All("c", F.Id("Bool"),
            Equal(Call("U", x, c), Call("if", c, horizontal, vertical)))));
    }

    private static Formula StarFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"),
            xu = Field(x, "u"), xv = Field(x, "v"), xd = Field(x, "d"),
            yu = Field(y, "u"), yv = Field(y, "v"), yd = Field(y, "d");
        Formula seam = Seq(Open, Multiply(xu, yv), Minus, Multiply(xv, yu), Close);
        return Disp(All("x", F.Id("Five"), All("y", F.Id("Five"),
            Equal(Call("star", x, y), Tuple(
                Seq(xu, Plus, yu), Seq(xv, Plus, yv), Seq(xd, Plus, yd, Plus, seam),
                Seq(Field(x, "e"), Plus, Field(y, "e"), Plus, D(3), Open,
                    Multiply(yd, xu), Minus, Multiply(xd, yu), Close, Plus, seam, Open, xu, Minus, yu, Close),
                Seq(Field(x, "f"), Plus, Field(y, "f"), Plus, D(3), Open,
                    Multiply(yd, xv), Minus, Multiply(xd, yv), Close, Plus, seam, Open, xv, Minus, yv, Close))))));
    }

    private static Formula AppendFormula()
    {
        Formula w = F.Id("w"), c = F.Id("c");
        return Disp(All("w", WordType(), All("c", F.Id("Bool"), Equal(
            Call("G", Append(w, Seq(OpenBracket, c, CloseBracket))),
            Call("U", Call("G", w), c)))));
    }

    private static Formula ConcatFormula()
    {
        Formula h = F.Id("h"), k = F.Id("k");
        return Disp(All("h", WordType(), All("k", WordType(), Equal(
            Call("G", Append(h, k)), Call("star", Call("G", h), Call("G", k))))));
    }

    private static Formula ReverseFormula()
    {
        Formula w = F.Id("w"), g = Call("G", w);
        return Disp(All("w", WordType(), Equal(Call("G", Call("reverse", w)),
            Tuple(Field(g, "u"), Field(g, "v"), Seq(Minus, Field(g, "d")),
                Field(g, "e"), Field(g, "f")))));
    }

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
