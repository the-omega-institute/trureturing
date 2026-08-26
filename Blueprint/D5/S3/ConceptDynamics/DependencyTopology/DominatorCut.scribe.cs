using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DependencyTopology;

internal sealed class DominatorCutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A dominator is a vertex whose deletion cuts every rooted path to its target.",
        H("Dominator Cut"),
        Blocks(Describe.Lean(
            DescribeId.Create("deleting-a-proper-dominator-cuts-all-paths"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/DependencyTopology/DominatorCut."
                    + "unreachable_after_delete_of_dominates"),
            H("Deleting a proper dominator makes the target unreachable"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Dominates means that every directed path from the root to the target "
                        + "contains the designated vertex.")),
                Paragraph(Text(
                    "Deleting that vertex retains only edges whose endpoints are both "
                        + "different from it. Any path in the deleted graph maps back to an "
                        + "original path that avoids the deleted vertex.")),
                Paragraph(Text(
                    "When the dominator is distinct from the target, such an avoiding path "
                        + "contradicts dominance. Therefore the deleted graph has no rooted "
                        + "directed path to the target."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula TheoremFormula()
    {
        Formula vertex = F.Id("V");
        Formula edge = F.Id("edge");
        Formula root = F.Id("root");
        Formula dominator = F.Id("u");
        Formula target = F.Id("v");
        Formula hypotheses = Seq(
            Call("Dominates", root, edge, dominator, target), Sp, Land, Sp,
            dominator, Sp, Neq, Sp, target);
        Formula deletedPath = Call(
            "DirectedPath",
            Call("deleteVertex", edge, dominator),
            root,
            target);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, edge, Colon, Sp,
            Arrow(vertex, Arrow(vertex, Seq(Operatorname, Grp(F.Id("Prop"))))),
            Comma, RowBreak, Grp(),
            root, Comma, Sp, dominator, Comma, Sp, target,
            Colon, Sp, vertex, Comma, RowBreak, Grp(),
            Open, hypotheses, Close, Sp, Rightarrow, RowBreak, Grp(),
            Neg, Sp, Call("Nonempty", deletedPath), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
