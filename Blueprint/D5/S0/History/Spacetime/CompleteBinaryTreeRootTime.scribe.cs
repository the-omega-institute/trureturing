using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Spacetime;

internal sealed class CompleteBinaryTreeRootTimeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite complete binary tree propagates leaf times by a unit delay per edge.",
        H("Complete Binary Tree Root Time"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("root-time-is-maximum-leaf-time-plus-depth"),
                DeclarationHandle.Create(
                    "D5/S0/History/Spacetime/CompleteBinaryTreeRootTime."
                    + "rootTime_eq_max_leaf_time_add_depth"),
                H("Root time is the maximum of leaf time plus depth"),
                StatementSource.FromAuthor(RootTimeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The CompleteBinaryTree carrier has integer-valued leaves and exactly two "
                        + "children at every internal node. The root rule takes the larger child "
                        + "time and adds one. Its finite leaf records carry both the input time and "
                        + "the number of edges from the current root. The theorem proves that the "
                        + "root time is the maximum of time plus depth over those records.")),
                    Paragraph(Text(
                        "The proof is structural induction. At an internal node, every leaf record "
                        + "receives one additional depth unit, and translation by one commutes with "
                        + "the finite maximum. Lean compares the integer root time, coerced into "
                        + "WithBot integers, with List.maximum of the leaf scores. Every such tree "
                        + "has at least one leaf, so this represents the ordinary finite maximum. "
                        + "The statement concerns this construction tree only: archived events "
                        + "outside the tree can have later times, so this is not the maximum of "
                        + "the entire archive or a physical time law."))),
                DescribeRole.Proposition))));

    private static Formula RootTimeFormula()
    {
        Formula rootTime = new Formula.Subscript(
            F.Id("t"),
            Seq(F.Mathrm, Grp(F.Id("root"))));
        Formula leafTime = new Formula.Subscript(F.Id("t"), F.Id("i"));
        Formula leafDepth = new Formula.Subscript(
            Seq(F.Operatorname, Grp(F.Id("depth"))),
            F.Id("i"));
        Formula maximum = new Formula.Subscript(F.Max, F.Id("i"));
        Formula summand = new Formula.Binary(
            leafTime,
            FormulaBinaryOperator.Add,
            leafDepth);
        return Disp(Seq(
            rootTime,
            Sp,
            Eq,
            Sp,
            maximum,
            Sp,
            Open,
            summand,
            Close,
            Dot));
    }
}
