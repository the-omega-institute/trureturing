using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class NiuQ15TableauxDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/niu2026firstdescent");

    public DocumentDefinition Create()
    {
        var k = V("k");
        var n = V("n");
        var r = V("r");
        var m = V("m");
        var i = V("i");
        var j = V("j");
        var t = V("t");
        var p = V("p");
        var shape = V("shape");
        var hn = V("hn");
        var kRows = Call("RowShape", k);
        var finK = Call("Fin", k);
        var rows = Seq(shape, Dot, V("rows"));
        var cell = Call("Cell", shape);
        var size = Call("size", shape);
        var removable = Call("RemovableRow", shape);
        var erased = Call("eraseRowEnd", shape, i);
        var tableau = Call("StandardTableau", shape);
        var rectangle = Call("rectangle", k, n);
        var rotated = Call("rotatedShape", k, n, r);
        var secondRow = Call("secondRowFirst", hn);
        var rectWithSecondRow = Call("rectangle", Add(k, D(1)), n);
        var rectTableau = Call("StandardTableau", rectWithSecondRow);
        var rotatedTableau = Call("StandardTableau", Call("rotatedShape", Add(k, D(1)), n, r));
        var descent = Call("firstDescent", hn, t);
        var tail = NatCard(Subtype(t, rectTableau, AtMost(r, descent)));
        var point = NatCard(Subtype(t, rectTableau, Equal(descent, r)));
        var nextTail = NatCard(Subtype(t, rectTableau, AtMost(Add(r, D(1)), descent)));
        var positiveWidth = Lt(D(0), n);
        var label = V("e");
        return DocumentDefinition.Create(ScribeNode.Create(
            "Standard tableaux, removable-row deletion and the rectangle survival event.",
            H("Tableaux, Deletion and Rectangle Rotation"),
            Blocks(
                Def("RowShape", "Straight shapes",
                    All("shape", kRows, HasType(rows, new Formula.TypeArrow(finK, NatType()))),
                    "A shape carries the row lengths and a proof that they are antitone, allowing trailing zero lengths."),
                Def("Cell", "Cells of a shape",
                    Equal(cell, Subtype(p, Seq(finK, Sp, Times, Sp, NatType()),
                        Lt(Proj(p, 2), Apply(rows, Proj(p, 1))))),
                    "The row and column both start at zero."),
                Def("instPartialOrderCell", "Cell order", Call("PartialOrder", cell),
                    "The order is the restriction of the coordinatewise partial order on the row and column indices."),
                Def("size", "Number of cells",
                    Equal(size, IndexedSum(i, finK, Apply(rows, i))),
                    "The sum includes every row slot."),
                Def("Labeling", "Strictly increasing labels",
                    Equal(Call("Labeling", p, m),
                        Subtype(label, new Formula.Relation(p, FormulaRelationOperator.Equivalent, Call("Fin", m)),
                            Call("StrictMono", label))),
                    "The carrier p is any preordered type. The labels are a bijection to the zero-based labels in Fin m."),
                Def("StandardTableau", "Standard tableaux",
                    Equal(tableau, Call("Labeling", cell, size)),
                    "The strict order condition gives increase along rows and columns."),
                Def("instFintypeStandardTableau", "Finite tableau type", Call("Fintype", tableau),
                    "The type of strictly increasing bijections between the finite cell and label types is finite."),
                Def("RemovableRow", "Removable rows",
                    Equal(removable, Subtype(i, finK, And(Lt(D(0), Apply(rows, i)),
                        Parenthesized(All("j", finK, Imp(Lt(i, j), Lt(Apply(rows, j), Apply(rows, i)))))))),
                    "The row must be positive and every lower row must be shorter."),
                Def("instFintypeRemovableRow", "Finite removable row type", Call("Fintype", removable),
                    "Removable rows form a subtype of Fin k."),
                Def("eraseRowEnd", "Shorten a removable row",
                    All("i", removable, All("j", finK,
                        Equal(Apply(Seq(Parenthesized(erased), Dot, V("rows")), j),
                            Call("ite", Equal(j, Proj(i, 1)), Subtract(Apply(rows, j), D(1)), Apply(rows, j))))),
                    "The shortened profile remains antitone. Subtraction is in the naturals."),
                Thm("size_eraseRowEnd", "The shortened diagram loses one cell",
                    OnShape(All("i", removable, Equal(Add(Call("size", erased), D(1)), size))),
                    "Only the selected positive row loses one cell."),
                Thm("card_standardTableau_eq_sum", "Cardinality recurrence",
                    OnShape(Imp(Lt(D(0), size), Equal(Card(tableau),
                        IndexedSum(i, removable, Card(Call("StandardTableau", erased)))))),
                    "Removing the maximum label gives a bijection with a choice of removable row and a tableau on the shortened diagram."),
                Thm("card_standardTableau_of_size_zero", "Empty tableau",
                    OnShape(Imp(Equal(size, D(0)), Equal(Card(tableau), D(1)))),
                    "There is exactly one bijection between the two empty types."),
                Def("rectangle", "Rectangle",
                    All("i", Call("Fin", Add(k, D(1))), Equal(Apply(Seq(rectangle, Dot, V("rows")), i), n)),
                    "The shape rectangle(k,n) has k + 1 rows, each of length n."),
                Thm("size_rectangle", "Rectangle cardinality",
                    All("k", NatType(), All("n", NatType(),
                        Equal(Call("size", rectangle), Multiply(Parenthesized(Add(k, D(1))), n)))),
                    "This includes width zero."),
                Def("rotatedShape", "Shortened rectangle",
                    All("i", Call("Fin", Add(k, D(1))),
                        Equal(Apply(Seq(rotated, Dot, V("rows")), i),
                            Call("ite", Equal(i, Call("last", k)), Subtract(n, r), n))),
                    "Only the bottom row loses r cells, with natural subtraction defined also for r > n."),
                Def("secondRowFirst", "First cell of the second row",
                    ProofBinder("hn", positiveWidth, Equal(Proj(secondRow, 1), Parenthesized(Seq(D(1), Comma, Sp, D(0))))),
                    "Positive width ensures that the coordinate pair lies in the cell subtype."),
                Node("firstDescent", "First descent",
                    ProofBinder("hn", positiveWidth, All("t", rectTableau,
                        Equal(descent, Call("val", Apply(Proj(t, 1), secondRow))))),
                    "The value of the zero-based label equals the published one-based entry minus one.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Thm("firstDescent_le_width", "The first descent lies within the width",
                    RectangleVariables(ProofBinder("hn", positiveWidth, All("t", rectTableau, AtMost(descent, n)))),
                    "Labels before the second-row first entry lie in the top row."),
                Thm("card_rectangle_tail", "Count of the survival event",
                    RectangleVariables(All("r", NatType(),
                        ProofBinder("hn", positiveWidth, Imp(AtMost(r, n), Equal(tail, Card(rotatedTableau)))))),
                    "Delete the first r cells of the top row and rotate the complement to a straight shape."),
                Thm("card_rectangle_tail_of_width_lt", "Empty survival event above the width",
                    RectangleVariables(All("r", NatType(),
                        ProofBinder("hn", positiveWidth, Imp(Lt(n, r), Equal(tail, D(0)))))),
                    "The threshold exceeds every possible descent."),
                Thm("rectangle_card_pos", "Nonempty rectangle tableau type",
                    RectangleVariables(Lt(D(0), Card(Call("StandardTableau", rectangle)))),
                    "Row-major labels give a tableau, including at width zero."),
                Thm("card_rectangle_tail_eq_point_add_next", "Partition into a point and the next tail",
                    RectangleVariables(ProofBinder("hn", positiveWidth,
                        All("r", NatType(), Equal(tail, Add(point, nextTail))))),
                    "At threshold r the tableau either has descent r or survives the next threshold.")
            ), []));
    }

    private static DocumentBlock Def(string name, string title, Formula formula, string prose) =>
        Node(name, title, formula, prose, DescribeRole.Definition);
    private static DocumentBlock Thm(string name, string title, Formula formula, string prose) =>
        Node(name, title, formula, prose, DescribeRole.Theorem);
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("niuq15tableaux-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula NatType() => Seq(Mathbb, Grp(V("N")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Proj(Formula x, byte i) => Seq(x, Dot, D(i));
    private static Formula Apply(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula ProofBinder(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(HasType(V(name), type)), Comma, Sp, body);
    private static Formula HasType(Formula value, Formula type) => Seq(value, Sp, Colon, Sp, type);
    private static Formula OnShape(Formula body) => All("k", NatType(), All("shape", Call("RowShape", V("k")), body));
    private static Formula RectangleVariables(Formula body) => All("k", NatType(), All("n", NatType(), body));
    private static Formula Subtype(Formula x, Formula type, Formula condition) =>
        new Formula.SetLiteral([Seq(HasType(x, type), Sp, Mid, Sp, condition)]);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Card(Formula x) => Apply(Qualified("Fintype", "card"), x);
    private static Formula NatCard(Formula x) => Apply(Qualified("Nat", "card"), x);
    private static Formula IndexedSum(Formula x, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(x, Sp, InMacro, Sp, type)), Sp, body);
}
