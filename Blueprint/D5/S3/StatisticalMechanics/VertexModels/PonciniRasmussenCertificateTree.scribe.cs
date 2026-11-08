using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.VertexModels;

internal sealed class PonciniRasmussenCertificateTreeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenCertificateTree.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shared certificate trees", H("Shared certificate trees"), Blocks(
            Node("Tree", Typed(Name("Tree"), new Formula.TypeArrow(Name("Type"), Name("Type"))),
                "D5.S3.StatisticalMechanics.PonciniRasmussenCertificateTree.Tree is the " +
                "shared inductive type. For α : Type its constructors are " +
                "Tree.leaf : α → Tree α and Tree.node : Tree α → Tree α → Tree α. " +
                "The diagram tables, incoming row table and Horner state trees use this type."),
            Node("get", All("α", Name("Type"), new Formula.Logic(
                All("a", Id("α"), All("j", Name("Nat"),
                    Equal(Call("get", Call("Tree.leaf", Id("a")), Id("j")), Id("a")))),
                FormulaLogicOperator.And,
                All("l", Tree(), All("r", Tree(), All("j", Name("Nat"),
                    Equal(Call("get", Call("Tree.node", Id("l"), Id("r")), Id("j")),
                        Call("ite", Equal(Call("Nat.mod", Id("j"), Num(2)), Num(0)),
                            Call("get", Id("l"), Call("Nat.div", Id("j"), Num(2))),
                            Call("get", Id("r"), Call("Nat.div", Id("j"), Num(2)))))))))),
                "D5.S3.StatisticalMechanics.PonciniRasmussenCertificateTree.get reads a " +
                "natural index by parity and division by two. A leaf returns its value " +
                "at every remaining index. The shared prb1_tree_data% elaborator preserves " +
                "the expected type while disabling the information tree for literal data."))));

    private static Formula Name(string name) => Id(name);
    private static Formula Tree() => Call("Tree", Id("α"));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Name(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static DocumentBlock Node(string name, Formula formula, string prose) => Describe.Lean(
        DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(name),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
