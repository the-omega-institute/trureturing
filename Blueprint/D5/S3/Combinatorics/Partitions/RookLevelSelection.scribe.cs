using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class RookLevelSelectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/RookLevelSelection.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A recursive cell bijection counts full rook selections in nested complete lower levels.",
        H("Full selection in nested levels"), Blocks(
            Definition("NestedFull", "The exact lower-level hypothesis",
                "Levels are indexed from top to bottom. For every earlier level i and later level j, if a cell with column c occurs in level i, then all m cells of column c occur in level j. The column type C is arbitrary finite, with decidable equality. Each level is a finite set of pairs in C times Fin(m)."),
            Definition("Selections", "Actual full rook selections",
                "A selection is a function choosing one member of each level set, with an injective column projection. Thus every level has exactly one rook and no column has two. Within-level rows are actual Fin(m) values, not a formal weight."),
            Describe.Lean(DescribeId.Create("rooklevelselection-count"), DeclarationHandle.Create(Prefix + "selections_count"),
                H("The falling level product"), StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed fallingLevelProduct(m,L) means the product over i in Fin(n) of card(L(i)) minus m times val(i), using natural truncated subtraction. To prove the count, split a nonempty selection into its top cell and the remaining selection with that entire column removed. The chosen top column contributes exactly m cells to every lower level by NestedFull. Removing it preserves NestedFull and reduces every remaining level cardinality by m. The split and reassembly are inverse on the actual cell functions. Induction gives the product, including empty levels, zero m and impossible selections. The theorem is consumed by the actual Ferrers augmentation in RookAugmentedLevels; it is not an assumption of that application."))), DescribeRole.Theorem)
        ), []));
    private static DocumentBlock Definition(string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create("rooklevelselection-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula I(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(I(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Statement()
    {
        Formula m = I("m"), n = I("n"), c = I("C"), l = I("L"), nat = I("Nat");
        Formula cells = Call("Finset", Call("Prod", c, Call("Fin", m)));
        Formula equality = new Formula.Relation(Call("card", Call("Selections", m, l)),
            FormulaRelationOperator.Equal, Call("fallingLevelProduct", m, l));
        Formula law = new Formula.Logic(Call("NestedFull", m, l), FormulaLogicOperator.Implies, equality);
        Formula body = All("m", nat, All("n", nat, All("L", new Formula.TypeArrow(Call("Fin", n), cells), law)));
        return All("C", I("Type"), Seq(OpenBracket, Call("Fintype", c), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", c), CloseBracket, Sp, body));
    }
}
