using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class NiuTableauCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/NiuTableauCount.";

    public DocumentDefinition Create()
    {
        var k = V("k");
        var i = V("i");
        var j = V("j");
        var rows = V("rows");
        var b = V("b");
        var finK = Call("Fin", k);
        var rowType = new Formula.TypeArrow(finK, NatType());
        var node = Call("shiftedNode", rows, i);
        var deleted = Call("deleteRow", rows, i);
        var removable = Call("RemovableRow", rows, i);
        var count = Call("shiftedCount", rows);
        var total = Indexed(Sum, j, finK, Apply(rows, j));
        var van = Call("vandermonde", LambdaOf(i, finK, Call("cast", node)));
        var columnProduct = Indexed(Prod, j, Call("Ioi", i),
            Parenthesized(Subtract(Apply(b, i), Apply(b, j))));
        var empty = LambdaOf(i, finK, D(0));
        var deletionSum = Indexed(Sum, i,
            Call("filter", Call("RemovableRow", rows), V("univ")), Call("shiftedCount", deleted));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The rational shifted-node formula obeys the same deletion recurrence as the number of standard tableaux of a straight shape.",
            H("Row Deletion for the Shifted Vandermonde Formula"),
            Blocks(
                Node("niu-tableau-delete-row", "Delete a cell", "deleteRow",
                    Equal(deleted, Call("update", rows, i, Subtract(Apply(rows, i), D(1)))),
                    "Subtract one in the naturals from the selected row length and retain all k row slots.",
                    DescribeRole.Definition),
                Node("niu-tableau-removable-row", "Removable rows", "RemovableRow",
                    new Formula.Logic(removable, FormulaLogicOperator.Iff,
                        Parenthesized(new Formula.Logic(Lt(D(0), Apply(rows, i)), FormulaLogicOperator.And,
                            Parenthesized(All("j", finK, Imp(Lt(i, j), Lt(Apply(rows, j), Apply(rows, i)))))))),
                    "A removable row is positive and strictly longer than every row below it.", DescribeRole.Definition),
                Node("niu-tableau-shifted-node", "Shifted row length", "shiftedNode",
                    Equal(node, Add(Apply(rows, i), Call("val", Call("rev", i)))),
                    "The value of the reversed finite index is the number of row slots below i.", DescribeRole.Definition),
                Node("niu-tableau-vandermonde", "Vandermonde product", "vandermonde",
                    All("b", new Formula.TypeArrow(finK, RatType()),
                        Equal(Call("vandermonde", b), Indexed(Prod, i, finK, columnProduct))),
                    "The inner product ranges over j greater than i.", DescribeRole.Definition),
                Node("niu-tableau-shifted-count", "Shifted-node formula", "shiftedCount",
                    All("rows", rowType,
                        Equal(count, new Formula.Fraction(
                            Multiply(Call("cast", Call("factorial", total)), van),
                            Indexed(Prod, i, finK, Call("cast", Call("factorial", node)))))),
                    "All factorials are formed in the naturals. The displayed product and division are in the rationals.",
                    DescribeRole.Definition),
                Node("niu-tableau-decidable-removable-row", "Decidability of a removable row",
                    "instDecidableRemovableRow",
                    All("k", NatType(), All("rows", rowType, All("i", finK, Call("Decidable", removable)))),
                    "Each comparison and the quantifier over the finite row indices are decidable.", DescribeRole.Definition),
                Node("niu-tableau-empty-count", "Empty diagram", "shiftedCount_empty",
                    All("k", NatType(), Equal(Call("shiftedCount", empty), D(1))),
                    "For fixed i the differences with later rows run through 1 up to its shifted node and cancel its factorial.",
                    DescribeRole.Theorem),
                Node("niu-tableau-count-recurrence", "One-cell deletion recurrence", "shiftedCount_recurrence",
                    All("k", NatType(), Imp(AtMost(D(2), k), All("rows", rowType,
                        Imp(Call("Antitone", rows), Imp(Lt(D(0), total), Equal(count, deletionSum)))))),
                    "The Vandermonde factors involving each row give its deletion weight. Nonremovable rows have weight zero. Polynomial interpolation shows that the sum of all weights is the total size.",
                    DescribeRole.Theorem)
            ), []));
    }

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula NatType() => Seq(Mathbb, Grp(V("N")));
    private static Formula RatType() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Apply(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula LambdaOf(Formula x, Formula type, Formula body) =>
        Parenthesized(Seq(x, Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Indexed(Formula op, Formula index, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(op, Seq(index, Sp, InMacro, Sp, domain)), Sp, body);
}
