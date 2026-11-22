using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Lattices.Tamari;

internal sealed class TreeRotationsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Lattices/Tamari/TreeRotations.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contextual right rotations generate the coordinate order on tree brackets.",
        H("Contextual rotations and tree bracket coordinates"),
        Blocks(
            Describe.Lean(DescribeId.Create("full-tree"),
                DeclarationHandle.Create(Owner + "FullTree"), H("Full binary trees"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("FullTree is Mathlib’s BinaryTree Unit. An empty node is a leaf."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("trees"),
                DeclarationHandle.Create(Owner + "Trees"), H("Trees at a fixed rank"),
                StatementSource.FromAuthor(F.Disp(Bind(FormulaQuantifier.ForAll, "m", NatType,
                    Rel(Call("Trees", F.Id("m")), FormulaRelationOperator.Equal, Seq(OpenBrace, F.Id("t"), Sp,
                    Mid, Sp, Logic(Rel(F.Id("t"), FormulaRelationOperator.MemberOf, F.Id("FullTree")),
                    FormulaLogicOperator.And, Rel(Call("numNodes", F.Id("t")), FormulaRelationOperator.Equal,
                    F.Id("m"))), CloseBrace))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Trees(m) contains exactly the full trees with m internal nodes and hence m + 1 leaves."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tree-brackets"),
                DeclarationHandle.Create(Owner + "treeBrackets"), H("Inorder endpoints"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At each internal inorder index, record the rightmost internal index of the subtree rooted there."
                    + " The resulting function is a bracketing function."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("right-rotation"),
                DeclarationHandle.Create(Owner + "RightRotation"), H("A right rotation in context"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The root step takes ((X Y) Z) to (X (Y Z)). A step in either child also gives a step on the"
                    + " whole tree with the other child fixed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("rotation-reach"),
                DeclarationHandle.Create(Owner + "RotationReach"), H("Rotation reachability"),
                StatementSource.FromAuthor(F.Disp(Rel(F.Id("RotationReach"), FormulaRelationOperator.Equal,
                    Call("ReflTransGen", F.Id("RightRotation"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("RotationReach is the reflexive transitive closure of RightRotation."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("rotation-reach-iff-bracket-le"),
                DeclarationHandle.Create(Owner + "rotationReach_iff_bracket_le"), H("Reachability equals bracket order"),
                StatementSource.FromAuthor(F.Disp(Bind(FormulaQuantifier.ForAll, "m", NatType,
                    Bind(FormulaQuantifier.ForAll, "t", Call("Trees", F.Id("m")),
                    Bind(FormulaQuantifier.ForAll, "u", Call("Trees", F.Id("m")), Logic(Call("RotationReach",
                    Call("val", F.Id("t")), Call("val", F.Id("u"))), FormulaLogicOperator.Iff,
                    Parenthesized(Rel(Call("treeBrackets", F.Id("t")), FormulaRelationOperator.LessThanOrEqual,
                    Call("treeBrackets", F.Id("u")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A rotation increases one endpoint. Conversely, at the first unequal coordinate one can rotate"
                    + " while staying below the target bracket. The sum of remaining endpoint deficits decreases."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tamari-partial-order"),
                DeclarationHandle.Create(Owner + "tamariPartialOrder"), H("The Tamari partial order"),
                StatementSource.FromAuthor(F.Disp(Bind(FormulaQuantifier.ForAll, "m", NatType,
                    Bind(FormulaQuantifier.ForAll, "t", Call("Trees", F.Id("m")),
                    Bind(FormulaQuantifier.ForAll, "u", Call("Trees", F.Id("m")),
                    Logic(Parenthesized(Rel(F.Id("t"), FormulaRelationOperator.LessThanOrEqual, F.Id("u"))),
                    FormulaLogicOperator.Iff, Call("RotationReach", Call("val", F.Id("t")), Call("val",
                    F.Id("u"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The order relation on fixed-rank trees is RotationReach on the underlying trees."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tree-bracket-order-iso"),
                DeclarationHandle.Create(Owner + "treeBracketOrderIso"), H("The tree bracket order isomorphism"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Inorder endpoint arrays determine their tree. Tree reconstruction gives every bracket array, and"
                    + " the rotation criterion identifies the two orders."))), DescribeRole.Definition))));

    private static Formula Call(string name, params Formula[] values) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. values]);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula domain, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), domain, body);

    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);

    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(left, op, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula NatType => Seq(Mathbb, Grp(F.Id("N")));
}
